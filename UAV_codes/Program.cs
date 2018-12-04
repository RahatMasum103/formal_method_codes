using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.IO;
using System.Diagnostics;
//using System.Linq;


/* Version 5
 * 
 * Fuel model (including refueling) is formalized.
 * Resilient (k different UAVs) Surveillance is formalized
 * 
 * [If it is ensure that each UAV return back to its initial position at the end of the analysis period with 
 * a remaining fuel no less than the initial stored fuel, the same trajectory can be continued to follow till
 * the criticalities of the transmission lines change.]
 * 
 * At some points, the UAVs may not be able to set for refueling.
 * 
 * TODO: To find the minimum number of UAVs that can do the continuous and resilient surveillance, the "UAV" 
 * parameter (whether alive or not) can be leveraged if z3 Opt is used (minimum number of live UAVs). 
 * 
 * TODO: Should we go backward direction only; such as: IT IS NOT HELPING
 * UavRefuel -->, UavRefueling -->, UavReturn -->, UavVisitPoint -->
 * We have many in both directions without proper verification if both are needed.
 */
namespace UAV
{
    class UavSurveillance
    {
        Context z3;
        Solver slv;
        //Optimize slv;
        static TextWriter twTime, twUav, twUavPath, twResult, twRefuel;  //tw, 

        #region Constants
        const int NUM_BUS = 14;

        const int LINE_BUS = 2;
        //const int LINE_PROP = 2;      // Line properties
        const int UAV_PROP = 5;         // # of UAV properties
        //const int HoveringFCost = 1;  // For fuel co-efficient, if stays in same point
        //const int SegmentCoverFCost = 3;  // For fuel co-efficient, if goes from one point to another    
        const int nFailedUAVs = 0;      // Setting value for # of k failed UAVs

        const int MAX_REM_FUEL_FOR_REFUEL = 50; // The maximum remaining fuel (in percentage) to plan for refueling
                                                // SMALLER VALUES INCREASE THE RUNNING TIME. 

        const int MAX_DIGIT = 16;   // Used in converting z3 real (double) values

        const string MAX_EXEC_TIME = "60000000";
        #endregion

        #region Input Variables
        String line;
        String[] lineElemnt;
        String str;

        int nBuses, nLines, nPoints, nLinks, nUAVs, nTimeSteps;
        int visitTimeThres, minSurveillanceScore;

        int visitResiliency, visitResTimeThres, minResSurveillanceScore;
        // Visit resiliency specifies the different number of UAVs to visit a point within a threshold time (visitResTimeThres);

        int segmentLength;

        int[,] line_point;
        int[,] point_topo;

        //int[,] uav_prop;  // NOTE: It is better to define each properties separately, which makes it easy to 
        // refer to a property. Otherwise, it is hard to remember which index refers which property.        
        int[] uav_init_position;
        int[] uav_fuel_stored;
        int[] uav_fuel_capacity;
        int[] uav_fuel_fly_step;
        int[] uav_fuel_hover_step;

        int[] line_weight;
        int[] point_weight;
        int[] point_to_base_step;

        int totalWeight;

        Dictionary<int, int> dictionary = new Dictionary<int, int>();
        #endregion        

        #region Z3 Variables
        //IntExpr ScoreTh, ResScoreTh;
        //IntExpr TimeTh;
        BoolExpr[,,] UavPointVisit; // We should not consider the step as an index in the UAV point visit.
                                    // A variable can be there to specify the time units at which the UAV reach a point.                

        //BoolExpr[,] SegPoint;
        BoolExpr[,] Visited;
        IntExpr[,,] UavVisitDuring;   // If a point is visited by a (particular) UAV during [s, s + visitResTimeThres)

        BoolExpr[] Surveilled;
        BoolExpr[] InitSurveilled;
        BoolExpr[] SubsequentSurveilled;

        BoolExpr[] ResSurveilled;
        //BoolExpr[] SubsequentResSurveilled;

        BoolExpr[] Uav;
        IntExpr[] SurveilledInt;
        RealExpr[] SurveilledScore;

        IntExpr[] ResSurveilledInt;
        RealExpr[] ResSurveilledScore;

        IntExpr[] UavInt;
        IntExpr TotalUavAlive;

        RealExpr[,] UavFuelRem;
        RealExpr TotalSurveillanceScore, TotalResSurveillanceScore;

        BoolExpr[,,] UavRefuel;     // Move toward the base for refueling from a point on the transmission line
        BoolExpr[,] UavRefueling;   // The UAV is being refueled at the base
        //IntExpr[,] UavReturning;    // The point where the UAV is going to return
        BoolExpr[,,] UavReturn;     // Return from the base to a point on the transmission line
        #endregion               

        #region Utility Functions
        public long nCr(int n, int r)
        {
            // naive: return Factorial(n) / (Factorial(r) * Factorial(n - r));
            return nPr(n, r) / Factorial(r);
        }

        public long nPr(int n, int r)
        {
            // naive: return Factorial(n) / Factorial(n - r);
            return FactorialDivision(n, n - r);
        }

        private long FactorialDivision(int topFactorial, int divisorFactorial)
        {
            long result = 1;
            for (int i = topFactorial; i > divisorFactorial; i--)
                result *= i;
            return result;
        }

        private long Factorial(int i)
        {
            if (i <= 1) return 1;
            return i * Factorial(i - 1);
        }

        // Convert an z3 Real value into Double value
        public static double ToDouble(String doubleString)
        {
            // Set maxDigits based on your need
            int maxDigits = MAX_DIGIT;
            double val = 0.0;
            bool negSign = false;
            String[] parts;
            String[] parts2 = new String[2];

            if (doubleString[0] == '-')
                negSign = true;

            char[] delims = { '-', '/', ' ' };

            parts = doubleString.Split(delims, StringSplitOptions.RemoveEmptyEntries);
            if (parts.Length != 2)
            {
                if (parts.Length == 1)
                {
                    int res;

                    if (int.TryParse(parts[0], out res))
                        return negSign ? -res : res;

                    double dRes;
                    if (double.TryParse(parts[0], out dRes))
                        return negSign ? -res : res;
                }

                Console.WriteLine("ToDouble: Exit due to Wrong Input Format");
                Environment.Exit(0);
            }

            int numDigists;
            if (parts[0].Length > maxDigits || parts[1].Length > maxDigits)
            {
                if (parts[0].Length > parts[1].Length)
                {
                    numDigists = parts[0].Length;
                    parts[1] = parts[1].PadLeft(numDigists, '0');
                }
                else //if (parts[0].Length < parts[1].Length)
                {
                    numDigists = parts[1].Length;
                    parts[0] = parts[0].PadLeft(numDigists, '0');
                }
                //else
                //    numDigists = parts[0].Length;

                parts2[0] = parts[0].Remove(maxDigits);
                parts2[1] = parts[1].Remove(maxDigits);
            }
            else
            {
                parts2[0] = parts[0].ToString();
                parts2[1] = parts[1].ToString();
            }

            double part0 = Convert.ToDouble(parts2[0]);
            double part1 = Convert.ToDouble(parts2[1]);

            if (part1 > 0)
                val = part0 / part1;
            else
                val = part0;

            if (negSign)
                return -val;
            else
                return val;
        }
        #endregion

        #region Input
        void ReadInput()
        {
            char[] delims = { ' ', ',', '\t' };

            string fileName = String.Format("Input_{0}_Bus_N.txt", NUM_BUS);

            // Read a text file using StreamReader
            System.IO.StreamReader sr = new System.IO.StreamReader(fileName);

            #region Number of buses, lines, points, number of segments/links, segment length, UAVs, total time steps
            // Number of Buses, Number of Lines, Number of Points, Number of Segments, Segment Length in Steps, Number of UAVs, Total Time Units/Steps
            while (true)
            {
                if ((line = sr.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Initial Inputs");
                }
                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                lineElemnt = line.Split(delims);
                if (lineElemnt.Length != 7)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Initial Inputs");
                }

                nBuses = Convert.ToInt32(lineElemnt[0]);
                nLines = Convert.ToInt32(lineElemnt[1]);

                // NOTE: The Base is considered as a point (the LAST point)
                nPoints = Convert.ToInt32(lineElemnt[2]) + 1;

                nLinks = Convert.ToInt32(lineElemnt[3]);
                segmentLength = Convert.ToInt32(lineElemnt[4]);
                nUAVs = Convert.ToInt32(lineElemnt[5]);
                nTimeSteps = Convert.ToInt32(lineElemnt[6]);

                //Console.WriteLine("Buses: " + nBuses + ", lines: " + nLines + ", points: " + nPoints + ", UAVs: " + nUAVs + ", links: " + nLinks + ", and time-steps: " + nTimeSteps);
                //twResult.WriteLine("Buses: {0}, lines: {1}, points: {2}, segments: {3}, segment length: {4}," +
                //    " UAVs: {5}, and slots: {6}", nBuses, nLines, nPoints, nLinks, segmentLength, nUAVs, nTimeSteps);

                //twUavPath.WriteLine(nTimeSteps);

                break;
            }
            #endregion            

            #region Line properties
            line_weight = new int[nLines + 1];

            while (true)
            {
                if ((line = sr.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Line Criticality");
                }
                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                lineElemnt = line.Split(delims);
                if (lineElemnt.Length != nLines)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Line Criticality");
                }

                for (int j = 1; j <= nLines; j++)
                {
                    line_weight[j] = Convert.ToInt32(lineElemnt[j - 1]);
                }
                break;
            }
            #endregion

            #region Line creation with points/segments
            line_point = new int[nLines + 1, nPoints + 1];
            for (int i = 1; i <= nLines; i++)
            {
                for (int j = 1; j <= nPoints; j++)
                {
                    line_point[i, j] = -1;
                }
            }

            point_weight = new int[nPoints + 1];
            for (int i = 1; i <= nPoints; i++)
            {
                point_weight[i] = -1;
            }
            point_weight[nPoints] = 0;


            for (int i = 1; i <= nLines; i++)
            {
                while (true)
                {
                    if ((line = sr.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }
                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElemnt = line.Split(delims);
                    //Console.WriteLine("length_prpo"+ lineElemnt.Length);
                    for (int j = 1; j <= (lineElemnt.Length); j++)
                    {
                        //Console.WriteLine("line inside" + lineElemnt[j + 1]);
                        line_point[i, j] = Convert.ToInt32(lineElemnt[j - 1]);

                        if (line_weight[i] > point_weight[line_point[i, j]])
                            point_weight[line_point[i, j]] = line_weight[i];
                    }
                    break;
                }
            }

            // The points over a line
            totalWeight = 0;
            //Console.Write("Point criticality weights: ");
            //twResult.Write("Point criticality weights: ");
            for (int p = 1; p <= nPoints; p++)
            {
                //Console.Write("{0} ", point_weight[p]);
                //twResult.Write("{0} ", point_weight[p]);
                totalWeight += point_weight[p];
            }
            //Console.WriteLine();
            //Console.WriteLine("Total criticality weight: {0}", totalWeight);

            //twResult.WriteLine();
            //twResult.WriteLine("Total criticality weight: {0}", totalWeight);              

            // Point topology matrix creation
            point_topo = new int[nPoints + 1, nPoints + 1];
            for (int i = 1; i <= nPoints; i++)
            {
                for (int j = 1; j <= nPoints; j++)
                {
                    point_topo[i, j] = -1;
                }
            }

            for (int i = 1; i < nPoints; i++)
            {
                point_topo[i, nPoints] = 1;
                point_topo[nPoints, i] = 1;
            }

            for (int i = 1; i <= nLinks; i++)
            {
                while (true)
                {
                    if ((line = sr.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: Links");
                    }
                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElemnt = line.Split(delims);
                    //Console.WriteLine("\nlink now" + lineElemnt[0] + lineElemnt[1]);
                    point_topo[Convert.ToInt32(lineElemnt[0]), Convert.ToInt32(lineElemnt[1])] = i;
                    point_topo[Convert.ToInt32(lineElemnt[1]), Convert.ToInt32(lineElemnt[0])] = i;
                    break;
                }
            }

            // The points over a line
            for (int i = 1; i <= nPoints; i++)
            {
                int count = 0;
                for (int j = 1; j <= nPoints; j++)
                {
                    if (point_topo[i, j] != -1)
                    {
                        count++;
                    }
                }

                if (dictionary.ContainsKey(i)) continue;
                else
                {
                    dictionary.Add(i, count);
                }
            }
            #endregion

            #region UAV propoerties
            // Initial Point, Stored Fuel, Fuel Capacity, Mileage (Fuel/Step), Hovering Cost (Fuel/Step)
            uav_init_position = new int[nUAVs + 1];
            uav_fuel_stored = new int[nUAVs + 1];
            uav_fuel_capacity = new int[nUAVs + 1];
            uav_fuel_fly_step = new int[nUAVs + 1];
            uav_fuel_hover_step = new int[nUAVs + 1];

            for (int i = 1; i <= nUAVs; i++)
            {
                while (true)
                {
                    if ((line = sr.ReadLine()) == null)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: UAV properties");
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElemnt = line.Split(delims);
                    if (lineElemnt.Length != UAV_PROP)
                    {
                        throw new Exception("Exit due to Insufficient/Extra Input: UAV properties");
                    }

                    uav_init_position[i] = Convert.ToInt32(lineElemnt[0]);
                    uav_fuel_stored[i] = Convert.ToInt32(lineElemnt[1]);
                    uav_fuel_capacity[i] = Convert.ToInt32(lineElemnt[2]);
                    uav_fuel_fly_step[i] = Convert.ToInt32(lineElemnt[3]);
                    uav_fuel_hover_step[i] = Convert.ToInt32(lineElemnt[4]);

                    break;
                }
            }
            #endregion

            #region Distance from points to the base (a refueling) station 
            point_to_base_step = new int[nPoints + 1];

            while (true)
            {
                if ((line = sr.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Distance from Points to the Base");
                }

                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                lineElemnt = line.Split(delims);
                if (lineElemnt.Length != nPoints - 1)   // Should not counte the base point
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Distance from Points to the Base");
                }

                for (int i = 1; i < nPoints; i++)
                {
                    point_to_base_step[i] = Convert.ToInt32(lineElemnt[i - 1]);
                }
                point_to_base_step[nPoints] = 0;

                break;
            }
            #endregion

            #region Time threshold for the continuous surveillance
            while (true)
            {
                if ((line = sr.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }
                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                lineElemnt = line.Split(delims);
                if (lineElemnt.Length != 1)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Distance from Points to the Base");
                }

                visitTimeThres = Convert.ToInt32(lineElemnt[0]);

                break;
            }
            #endregion

            #region Resiliency requirements
            while (true)
            {
                if ((line = sr.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }
                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                lineElemnt = line.Split(delims);
                if (lineElemnt.Length != 2)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Distance from Points to the Base");
                }

                visitResiliency = Convert.ToInt32(lineElemnt[0]);
                visitResTimeThres = Convert.ToInt32(lineElemnt[1]);

                break;
            }
            #endregion

            #region Threshold scores
            while (true)
            {
                if ((line = sr.ReadLine()) == null)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Links");
                }
                line = line.Trim();
                if ((line.Length == 0) || line.StartsWith("#"))
                    continue;

                lineElemnt = line.Split(delims);
                if (lineElemnt.Length != 2)
                {
                    throw new Exception("Exit due to Insufficient/Extra Input: Distance from Points to the Base");
                }

                minSurveillanceScore = Convert.ToInt32(lineElemnt[0]);
                minResSurveillanceScore = Convert.ToInt32(lineElemnt[1]);

                break;
            }
            #endregion

            //Console.WriteLine("Input Done");
            //Console.WriteLine("========================");
        }
        #endregion

        #region initialization
        void Initialize()
        {
            try
            {
                IntExpr Zero = z3.MkInt(0);
                RealExpr ZeroR = z3.MkReal(0);

                //TimeTh = (IntExpr)z3.MkConst("TimeThreshold", z3.IntSort);
                //ScoreTh = (IntExpr)z3.MkConst("ScoreThreshold", z3.IntSort);               

                //slv.Assert(z3.MkEq(TimeTh, z3.MkInt(visitTimeThres)));
                //slv.Assert(z3.MkEq(ScoreTh, z3.MkInt(minSurveillanceScore)));

                // UAV visiting points and refueling
                UavPointVisit = new BoolExpr[nUAVs + 1, nPoints + 1, nTimeSteps + 1];
                UavRefuel = new BoolExpr[nUAVs + 1, nPoints + 1, nTimeSteps + 1];
                UavRefueling = new BoolExpr[nUAVs + 1, nTimeSteps + 1];
                //UavReturning = new IntExpr[nUAVs + 1, nTimeSteps + 1];
                UavReturn = new BoolExpr[nUAVs + 1, nPoints + 1, nTimeSteps + 1];

                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int p = 1; p <= nPoints; p++)
                    {
                        for (int s = 1; s <= nTimeSteps; s++)
                        {
                            str = String.Format("UavPointVisit_u{0}_p{1}_s{2}", u, p, s);
                            UavPointVisit[u, p, s] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                            str = String.Format("UavRefuel_u{0}_p{1}_s{2}", u, p, s);
                            UavRefuel[u, p, s] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                            str = String.Format("UavReturn_u{0}_p{1}_s{2}", u, p, s);
                            UavReturn[u, p, s] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                            // The points from which no UAV can set for refueling
                            if (point_to_base_step[p] < 0)
                            {
                                slv.Assert(z3.MkNot(UavRefuel[u, p, s]));
                                slv.Assert(z3.MkNot(UavReturn[u, p, s]));
                                //slv.Assert(z3.MkNot(z3.MkOr(UavRefuel[u, p, s], UavReturn[u, p, s])));
                            }

                            if (p == nPoints)
                            {
                                slv.Assert(z3.MkNot(UavRefuel[u, nPoints, s]));
                                slv.Assert(z3.MkNot(UavReturn[u, nPoints, s]));
                            }
                        }
                    }
                }

                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int s = 1; s <= nTimeSteps; s++)
                    {
                        str = String.Format("UavRefueling_u{0}_s{1}", u, s);
                        UavRefueling[u, s] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                        //str = String.Format("UavReturning_u{0}_s{1}", u, s);
                        //UavReturning[u, s] = (IntExpr)z3.MkConst(str, z3.IntSort);
                    }
                }

                // UAV alive?
                Uav = new BoolExpr[nUAVs + 1];
                UavInt = new IntExpr[nUAVs + 1];
                for (int u = 1; u <= nUAVs; u++)
                {
                    str = String.Format("Uav_{0}", u);
                    Uav[u] = (BoolExpr)z3.MkConst(str, z3.BoolSort);
                    str = String.Format("UavInt_{0}", u);
                    UavInt[u] = (IntExpr)z3.MkConst(str, z3.IntSort);
                }

                // Total number of alive UAVs 
                str = String.Format("TotalUavAlive");
                TotalUavAlive = (IntExpr)z3.MkConst(str, z3.IntSort);

                // Point visited in a step
                Visited = new BoolExpr[nPoints + 1, nTimeSteps + 1];
                for (int j = 1; j <= nPoints; j++)
                {
                    for (int k = 1; k <= nTimeSteps; k++)
                    {
                        str = String.Format("Visited_{0}_{1}", j, k);
                        Visited[j, k] = (BoolExpr)z3.MkConst(str, z3.BoolSort);
                    }
                }

                UavVisitDuring = new IntExpr[nUAVs + 1, nPoints + 1, nTimeSteps + 1];
                // An integer (0 or 1) representing if point p is visisted by UAV u during [s, s + visitResTimeThres)
                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int p = 1; p <= nPoints; p++)
                    {
                        for (int s = 1; s <= nTimeSteps; s++)
                        {
                            str = String.Format("UavVisitedDuring_{0}_{1}_{2}", u, p, s);
                            UavVisitDuring[u, p, s] = (IntExpr)z3.MkConst(str, z3.IntSort);
                        }
                    }
                }

                // Point covered (continuously and resilient)
                Surveilled = new BoolExpr[nPoints];
                InitSurveilled = new BoolExpr[nPoints];
                SubsequentSurveilled = new BoolExpr[nPoints];

                ResSurveilled = new BoolExpr[nPoints];
                //SubsequentResSurveilled = new BoolExpr[nPoints];

                SurveilledInt = new IntExpr[nPoints];
                SurveilledScore = new RealExpr[nPoints];

                ResSurveilledInt = new IntExpr[nPoints];
                ResSurveilledScore = new RealExpr[nPoints];

                for (int j = 1; j < nPoints; j++)
                {
                    str = String.Format("Surveilled_p{0}", j);
                    Surveilled[j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                    str = String.Format("InitSurveilled_p{0}", j);
                    InitSurveilled[j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);

                    str = String.Format("SubsequentSurveilled_p{0}", j);
                    SubsequentSurveilled[j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);


                    str = String.Format("ResSurveilled_p{0}", j);
                    ResSurveilled[j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);


                    str = String.Format("SurveilledInt_{0}", j);
                    SurveilledInt[j] = (IntExpr)z3.MkConst(str, z3.IntSort);

                    str = String.Format("SurveilledScore_{0}", j);
                    SurveilledScore[j] = (RealExpr)z3.MkConst(str, z3.RealSort);


                    str = String.Format("ResSurveilledInt_{0}", j);
                    ResSurveilledInt[j] = (IntExpr)z3.MkConst(str, z3.IntSort);

                    str = String.Format("ResSurveilledScore_{0}", j);
                    ResSurveilledScore[j] = (RealExpr)z3.MkConst(str, z3.RealSort);
                }

                str = String.Format("SurveilledScore_{0}", 0);  // This is important to sum the surveilled scores.
                SurveilledScore[0] = (RealExpr)z3.MkConst(str, z3.RealSort);

                str = String.Format("ResSurveilledScore_{0}", 0);  // This is important to sum the surveilled scores.
                ResSurveilledScore[0] = (RealExpr)z3.MkConst(str, z3.RealSort);

                // Score Surveillance                
                str = String.Format("SurveillanceScore");
                TotalSurveillanceScore = (RealExpr)z3.MkConst(str, z3.RealSort);

                str = String.Format("ResSurveillanceScore");
                TotalResSurveillanceScore = (RealExpr)z3.MkConst(str, z3.RealSort);


                // Operating Fuel                
                UavFuelRem = new RealExpr[nUAVs + 1, nTimeSteps + 1];
                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int s = 1; s <= nTimeSteps; s++)
                    {
                        str = String.Format("UavRemFuel_{0}_{1}", u, s);
                        UavFuelRem[u, s] = (RealExpr)z3.MkConst(str, z3.RealSort);
                    }
                }

                // Initial placement of a UAV
                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int p = 1; p <= nPoints; p++)
                    {
                        if (p == uav_init_position[u])
                        {
                            // If the UAV is alive
                            slv.Assert(z3.MkImplies(Uav[u], UavPointVisit[u, p, 1]));
                            slv.Assert(z3.MkImplies(z3.MkNot(Uav[u]), z3.MkNot(UavPointVisit[u, p, 1])));
                        }
                        else
                        {
                            slv.Assert(z3.MkNot(UavPointVisit[u, p, 1]));
                        }
                    }
                }
            }
            catch (Z3Exception ex)
            {
                Console.WriteLine("Z3 Managed Exception: " + ex.Message);
                Console.WriteLine("Stack trace: " + ex.StackTrace);
            }
        }
        #endregion

        #region Formalization
        void Formalize()
        {
            IntExpr One = z3.MkInt(1);
            IntExpr Zero = z3.MkInt(0);
            RealExpr ZeroR = z3.MkReal(0);

            try
            {
                #region UAVs Visit Points
                // At a particular time-step a UAV must be at a point
                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int s = 1; s <= nTimeSteps; s++)
                    {
                        BoolExpr[] BExprs = new BoolExpr[nPoints];

                        for (int p = 1; p <= nPoints; p++)
                        {
                            BExprs[p - 1] = UavPointVisit[u, p, s];
                        }

                        slv.Assert(z3.MkImplies(Uav[u], z3.MkOr(BExprs)));
                    }
                }

                // At a particular time-step a UAV can be at one point only
                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int p = 1; p <= nPoints; p++)
                    {
                        for (int s = 1; s <= nTimeSteps; s++)
                        {
                            BoolExpr[] point = new BoolExpr[nPoints - 1];
                            int k = 0;
                            for (int q = 1; q <= nPoints; q++)
                            {
                                if (q != p)
                                {
                                    point[k++] = UavPointVisit[u, q, s];
                                }
                            }

                            ////slv.Assert(z3.MkImplies(UavPointVisit[u, p, s], z3.MkNot(z3.MkOr(point))));

                            //// TODO: The following is not needed! [NO. THIS IS NEEDED]
                            //slv.Assert(z3.MkImplies(z3.MkNot(z3.MkOr(point)), UavPointVisit[u, p, s]));

                            BoolExpr BExpr = z3.MkAnd(z3.MkImplies(UavPointVisit[u, p, s], z3.MkNot(z3.MkOr(point))), z3.MkImplies(z3.MkNot(z3.MkOr(point)), UavPointVisit[u, p, s]));
                            slv.Assert(z3.MkImplies(Uav[u], BExpr));
                        }
                    }
                }

                // UAV visiting through segments 
                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int p = 1; p < nPoints; p++)   // Exclude the base point
                    {
                        for (int s = 2; s <= nTimeSteps; s++)
                        {
                            int value = dictionary[p];

                            BoolExpr[] visit = new BoolExpr[value - 1];
                            int v = 0;
                            for (int p2 = 1; p2 < nPoints; p2++)
                            {
                                // Checking if there is link/segment between points 
                                if (p == p2 || (point_topo[p2, p] == -1))
                                    continue;

                                BoolExpr Expr = UavPointVisit[u, p2, s - 1];

                                // NOTE: We do not need the following as the link is already checked.
                                //BoolExpr UvpE2 = SegPoint[h, p];                                
                                //visit[v] = z3.MkAnd(UvpE1, UvpE2);

                                visit[v] = Expr;

                                v++;
                            }

                            // TODO: Need to extend Uav[u] for Uav[u, s] //

                            // Fly to a (Different) Point
                            BoolExpr BExprDP = z3.MkAnd(z3.MkOr(visit),
                                z3.MkEq(UavFuelRem[u, s], z3.MkSub(UavFuelRem[u, s - 1], z3.MkReal(uav_fuel_fly_step[u]))));
                            //BoolExpr BExprDP = z3.MkOr(visit);

                            //// Hovering at the (Same) Point (REDUCED: Commented for efficiency)
                            //BoolExpr BExprSP = z3.MkAnd(UavPointVisit[u, p, s - 1],
                            //    z3.MkEq(UavFuelRem[u, s], z3.MkSub(UavFuelRem[u, s - 1], z3.MkReal(uav_fuel_hover_step[u]))));
                            ////BoolExpr BExprSP = UavPointVisit[u, p, s - 1];

                            //BoolExpr Expr2 = z3.MkOr(BExprDP, BExprSP); 
                            BoolExpr Expr2 = BExprDP;           // When you do not consider hovering/loitering

                            // Fuel Constraint
                            BoolExpr BExprF = z3.MkGe(UavFuelRem[u, s], z3.MkReal(Math.Abs(point_to_base_step[p]) * uav_fuel_fly_step[u]));     // FIXED: It was not checking the negative values (when we considers them)

                            slv.Assert(z3.MkImplies(UavPointVisit[u, p, s],
                                z3.MkAnd(Uav[u], z3.MkOr(UavReturn[u, p, s], z3.MkAnd(Expr2, BExprF)))));
                            //slv.Assert(z3.MkImplies(UavPointVisit[u, p, s], z3.MkAnd(Uav[u], Expr2, BExprF)));
                        }
                    }
                }
                #endregion

                #region Visited Points                
                //A point is visited at a time-step if ANY UAV visits it at that time
                for (int p = 1; p <= nPoints; p++)
                {
                    for (int s = 1; s <= nTimeSteps; s++)
                    {
                        BoolExpr[] Exprs = new BoolExpr[nUAVs];

                        for (int u = 1; u <= nUAVs; u++)
                        {
                            //uavVisit[u - 1] = UavPointVisit[u, p, s]; 
                            Exprs[u - 1] = UavPointVisit[u, p, s];
                        }

                        // A UAV visits the point at a particular time-step
                        //BoolExpr Expr = z3.MkImplies(Visited[p, s], z3.MkOr(Exprs));                        
                        slv.Assert(z3.MkImplies(Visited[p, s], z3.MkOr(Exprs)));

                        // TODO: The following is not needed! [YES, it is not needed. HOWEVER, We NEED it for better performance.]
                        slv.Assert(z3.MkImplies(z3.MkOr(Exprs), Visited[p, s]));
                    }
                }
                #endregion

                #region Continuous Visit within a Threshold Time
                // Initial visit within the threshold
                for (int p = 1; p < nPoints; p++)
                {
                    BoolExpr[] thresVisit = new BoolExpr[visitTimeThres];

                    for (int s = 1; s <= visitTimeThres; s++)   // initial visit within threshold
                    {
                        thresVisit[s - 1] = Visited[p, s];
                    }

                    slv.Assert(z3.MkImplies(InitSurveilled[p], z3.MkOr(thresVisit)));

                    //// TODO: The following is not needed!
                    //slv.Assert(z3.MkImplies(z3.MkOr(thresVisit), InitSurveilled[p]));
                }

                // Subsequent Visits within each threshold time interval
                for (int p = 1; p < nPoints; p++)
                {
                    BoolExpr[] SExprs = new BoolExpr[nTimeSteps - visitTimeThres];

                    for (int s = 1; s <= nTimeSteps - visitTimeThres; s++)
                    {
                        BoolExpr[] SExprs2 = new BoolExpr[visitTimeThres];

                        int i = 0;
                        for (int ns = s + 1; ns <= s + visitTimeThres; ns++)    // The next visit must be within visitTimeThres
                        {
                            SExprs2[i++] = Visited[p, ns];
                        }

                        SExprs[s - 1] = z3.MkImplies(Visited[p, s], z3.MkOr(SExprs2));
                    }

                    slv.Assert(z3.MkImplies(SubsequentSurveilled[p], z3.MkAnd(SExprs)));

                    //// TODO: The following is not needed!
                    //slv.Assert(z3.MkImplies(z3.MkAnd(SExprs), SubsequentSurveilled[p]));
                }

                // A point is surveilled if it is continuously visited within the threshold time
                for (int p = 1; p < nPoints; p++)
                {
                    slv.Assert(z3.MkImplies(Surveilled[p],
                        z3.MkAnd(InitSurveilled[p], SubsequentSurveilled[p])));

                    //// TODO: The following is not needed!
                    //slv.Assert(z3.MkImplies(z3.MkAnd(InitSurveilled[p], SubsequentSurveilled[p]), Surveilled[p]));
                }
                #endregion

                #region Resilient Visit within a Threshold Time     
                // If a point is visited by a particular UAV during [s, s + visitResTimeThres)
                for (int u = 1; u <= nUAVs; u++)
                {
                    for (int p = 1; p < nPoints; p++)
                    {
                        BoolExpr[] SExprs = new BoolExpr[nTimeSteps - visitResTimeThres + 1];
                        // The different (visitResiliency number of) visits must be within visitTimeThres (i.e., including the first visit)

                        for (int s = 1; s <= nTimeSteps - visitResTimeThres + 1; s++)
                        {
                            BoolExpr[] Exprs = new BoolExpr[visitResTimeThres];

                            //int i = 0;
                            //for (int ns = s; ns < s + visitResTimeThres; ns++)
                            for (int i = 0; i < visitResTimeThres; i++)  // If UAV u visits point p during [s, s + visitResTimeThres)
                            {
                                Exprs[i] = UavPointVisit[u, p, s + i];
                            }

                            SExprs[s - 1] = z3.MkAnd(z3.MkImplies(z3.MkOr(Exprs), z3.MkEq(UavVisitDuring[u, p, s], One)),
                                z3.MkImplies(z3.MkNot(z3.MkOr(Exprs)), z3.MkEq(UavVisitDuring[u, p, s], Zero)));
                        }

                        slv.Assert(z3.MkAnd(SExprs));
                    }
                }

                // Subsequent Visits within each threshold time interval                
                // NOTE: The initial visit is ensured during continuous surveillance requirement
                for (int p = 1; p < nPoints; p++)
                {
                    BoolExpr[] SExprs = new BoolExpr[nTimeSteps - visitResTimeThres + 1];

                    for (int s = 1; s <= nTimeSteps - visitResTimeThres + 1; s++)
                    // The different (visitResiliency number of) visits must be within visitTimeThres
                    {
                        IntExpr[] IExprs = new IntExpr[nUAVs];

                        for (int u = 1; u <= nUAVs; u++)
                        {
                            IExprs[u - 1] = UavVisitDuring[u, p, s];
                        }

                        SExprs[s - 1] = z3.MkImplies(Visited[p, s], z3.MkGe(z3.MkAdd(IExprs), z3.MkInt(visitResiliency)));
                    }

                    //slv.Assert(z3.MkImplies(ResSurveilled[p], z3.MkAnd(SExprs)));
                    slv.Assert(z3.MkImplies(ResSurveilled[p], z3.MkAnd(Surveilled[p], z3.MkAnd(SExprs))));   // NOTE: The point must be continuously surveilled as well

                    //// TODO: The following is not needed!
                    //slv.Assert(z3.MkImplies(z3.MkAnd(SExprs), ResSurveilled[p]));
                }
                #endregion                

                #region Initial (Remaining) Fuel and Refueling
                // Remaining fuel initialization and minimum remaining fuel invariant
                {
                    for (int u = 1; u <= nUAVs; u++)
                    {
                        slv.Assert(z3.MkEq(UavFuelRem[u, 1], z3.MkReal(uav_fuel_stored[u])));   // initial fuel given by input

                        for (int s = 1; s <= nTimeSteps; s++)
                        {
                            slv.Assert(z3.MkGe(UavFuelRem[u, s], ZeroR));
                        }
                    }
                }

                // Toward the base for refueling and returning to a point for performing surveillance
                {
                    for (int u = 1; u <= nUAVs; u++)
                    {
                        // A point from where go for refueling and returning back for performing surveillance
                        for (int p = 1; p < nPoints; p++)
                        {
                            if (point_to_base_step[p] < 0)  // Those points are only considered from which the UAV can go to the base.
                                continue;

                            for (int s = 1; s <= nTimeSteps - 2 * point_to_base_step[p]; s++)
                            {
                                int k = 2 * point_to_base_step[p];

                                // The steps to reach the base are abstracted.
                                BoolExpr[] BExprs = new BoolExpr[k];
                                for (int i = 1; i < k / 2; i++)
                                {
                                    BExprs[i - 1] = z3.MkAnd(UavPointVisit[u, nPoints, s + i], z3.MkNot(UavRefueling[u, s + i]),
                                        z3.MkEq(UavFuelRem[u, s + i], z3.MkSub(UavFuelRem[u, s + i - 1] - uav_fuel_fly_step[u])));
                                }
                                BExprs[k / 2 - 1] = z3.MkAnd(UavPointVisit[u, nPoints, s + k / 2], UavRefueling[u, s + k / 2],
                                    z3.MkEq(UavFuelRem[u, s + k / 2], z3.MkReal(uav_fuel_capacity[u])));

                                for (int i = k / 2 + 1; i < k; i++)
                                {
                                    BExprs[i - 1] = z3.MkAnd(UavPointVisit[u, nPoints, s + i], z3.MkNot(UavRefueling[u, s + i]),
                                        z3.MkEq(UavFuelRem[u, s + i], z3.MkSub(UavFuelRem[u, s + i - 1] - uav_fuel_fly_step[u])));
                                }

                                BExprs[k - 1] = z3.MkAnd(UavPointVisit[u, p, s + k], UavReturn[u, p, s + k],
                                        z3.MkEq(UavFuelRem[u, s + k], z3.MkSub(UavFuelRem[u, s + k - 1] - uav_fuel_fly_step[u])));

                                //slv.Assert(z3.MkImplies(UavRefuel[u, p, s], z3.MkAnd(UavPointVisit[u, p, s], z3.MkAnd(BExprs))));

                                // If we consider the remaining fuel constraint, comment the earlier one
                                // Earlier, the fuel constarint we asserted very late which in fact increased the execution time
                                slv.Assert(z3.MkImplies(UavRefuel[u, p, s], z3.MkAnd(UavPointVisit[u, p, s], z3.MkLe(UavFuelRem[u, s],
                                    z3.MkReal(uav_fuel_capacity[u] * MAX_REM_FUEL_FOR_REFUEL / 100)), z3.MkAnd(BExprs))));

                                //// TODO: The following is not needed! [YES, IT IS NOT NEEDED. IT ALSO HURTS THE PERFORMANCE.]
                                //slv.Assert(z3.MkImplies(z3.MkAnd(UavPointVisit[u, p, s], z3.MkAnd(BExprs)), UavRefuel[u, p, s]));
                            }

                            // The last steps at which refueling plan is assumed to be prohibited
                            {
                                // The steps at which there will be no refueling plan.
                                BoolExpr[] BExprs = new BoolExpr[2 * point_to_base_step[p]];

                                int i = 0;
                                for (int s = nTimeSteps - 2 * point_to_base_step[p] + 1; s <= nTimeSteps; s++)
                                {
                                    BExprs[i++] = z3.MkNot(UavRefuel[u, p, s]);
                                }

                                slv.Assert(z3.MkAnd(BExprs));
                            }
                        }
                    }
                }

                // A UAV will refuel only if it is at the base 
                {
                    for (int u = 1; u <= nUAVs; u++)
                    {
                        BoolExpr[] BExprs = new BoolExpr[nTimeSteps];
                        for (int s = 1; s <= nTimeSteps; s++)
                        {
                            //BExprs[s - 1] = z3.MkImplies(z3.MkNot(UavPointVisit[u, nPoints, s]), z3.MkNot(UavRefueling[u, s]));
                            BExprs[s - 1] = z3.MkImplies(UavRefueling[u, s], UavPointVisit[u, nPoints, s]);
                        }

                        slv.Assert(z3.MkAnd(BExprs));
                    }
                }

                // Returning to a point for performing surveillance (Commented)
                {
                    //for (int u = 1; u <= nUAVs; u++)
                    //{
                    //    for (int s = 1; s <= nTimeSteps; s++)
                    //    {
                    //        List<BoolExpr> LExprs = new List<BoolExpr>();

                    //        // A point where to be returned after the refueling to start surveillance
                    //        for (int p = 1; p < nPoints; p++)
                    //        {
                    //            int k = point_to_base_step[p];

                    //            if ((s + k) > nTimeSteps)
                    //                continue;

                    //            // UavReturning[u, s] can take one integer value and hence two or more return points should not satisfied
                    //            LExprs.Add(z3.MkEq(UavReturning[u, s], z3.MkInt(p)));
                    //        }

                    //        if (LExprs.Count > 0)
                    //            slv.Assert(z3.MkImplies(UavRefueling[u, s], z3.MkOr(LExprs)));
                    //        else
                    //            slv.Assert(z3.MkNot(UavRefueling[u, s])); // No refueling is possible in this case
                    //                                                      //slv.Assert(z3.MkImplies(UavRefueling[u, s], z3.MkEq(UavReturning[u, s], Zero)));

                    //        //slv.Assert(z3.MkImplies(z3.MkNot(UavRefueling[u, s]), z3.MkEq(UavReturning[u, s], Zero)));
                    //    }
                    //}

                    //for (int u = 1; u <= nUAVs; u++)
                    //{
                    //    for (int s = 1; s <= nTimeSteps; s++)
                    //    {
                    //        List<BoolExpr> LExprs = new List<BoolExpr>();

                    //        // A point where to be returned after the refueling to start surveillance
                    //        for (int p = 1; p < nPoints; p++)
                    //        {
                    //            if (point_to_base_step[p] <= 0)
                    //                continue;

                    //            int k = point_to_base_step[p];

                    //            //if ((s + k) > nTimeSteps)
                    //            //{
                    //            //    // The steps to return to a point from the base are abstracted.                                    
                    //            //    BoolExpr[] BExprs = new BoolExpr[nTimeSteps - s];
                    //            //    for (int i = 1; (s + i) <= nTimeSteps; i++)    // UavPointVisit at nPoints is already true for s
                    //            //    {
                    //            //        BExprs[i - 1] = z3.MkAnd(UavPointVisit[u, nPoints, s + i], z3.MkNot(UavRefueling[u, s + i]),
                    //            //            z3.MkEq(UavFuelRem[u, s + i], z3.MkSub(UavFuelRem[u, s + i - 1] - uav_fuel_fly_step[u])));
                    //            //    }
                    //            //    BoolExpr BExpr = z3.MkAnd(BExprs);

                    //            //    slv.Assert(z3.MkImplies(z3.MkAnd(UavRefueling[u, s], z3.MkEq(UavReturning[u, s], z3.MkInt(p))), BExpr));
                    //            //}
                    //            //else
                    //            if ((s + k) <= nTimeSteps)
                    //            {
                    //                // The steps to return to a point from the base are abstracted.                                    
                    //                BoolExpr[] BExprs = new BoolExpr[point_to_base_step[p] - 1];
                    //                for (int i = 1; i < k; i++)    // UavPointVisit at nPoints is already true for s
                    //                {
                    //                    BExprs[i - 1] = z3.MkAnd(UavPointVisit[u, nPoints, s + i], z3.MkNot(UavRefueling[u, s + i]),
                    //                        z3.MkEq(UavFuelRem[u, s + i], z3.MkSub(UavFuelRem[u, s + i - 1] - uav_fuel_fly_step[u])));
                    //                }
                    //                BoolExpr BExpr = z3.MkAnd(BExprs);

                    //                // When the UAV returns to p                                                     
                    //                BoolExpr BExpr2 = z3.MkAnd(UavReturn[u, p, s + k], UavPointVisit[u, p, s + k],
                    //                    z3.MkEq(UavFuelRem[u, s + k], z3.MkSub(UavFuelRem[u, s + k - 1] - uav_fuel_fly_step[u])));

                    //                slv.Assert(z3.MkImplies(z3.MkAnd(UavRefueling[u, s], z3.MkEq(UavReturning[u, s], z3.MkInt(p))),
                    //                    z3.MkAnd(BExpr, BExpr2)));

                    //                //// TODO: The following is not needed!
                    //                //slv.Assert(z3.MkAnd(z3.MkImplies(z3.MkAnd(BExpr, BExpr2),
                    //                //    z3.MkAnd(UavRefueling[u, s], z3.MkEq(UavReturning[u, s], z3.MkInt(p))))));
                    //            }
                    //        }
                    //    }
                    //}
                }

                // Refueling Plan Constraints (Commented)
                {
                    //for (int u = 1; u <= nUAVs; u++)
                    //{
                    //    // A point from where go for refueling
                    //    for (int p = 1; p < nPoints; p++)
                    //    {
                    //        for (int s = 1; s <= nTimeSteps; s++)
                    //        {
                    //            // A return to a point at a time cannot let the UAV go for another refuel plan at the same time
                    //            slv.Assert(z3.MkImplies(UavRefuel[u, p, s], z3.MkNot(UavReturn[u, p, s])));

                    //            //// The maximum remaining fuel (in percentage) to plan for refueling
                    //            //slv.Assert(z3.MkImplies(UavRefuel[u, p, s],
                    //            //    z3.MkLe(UavFuelRem[u, s], z3.MkReal(uav_fuel_capacity[u] * MAX_REM_FUEL_FOR_REFUEL / 100))));
                    //        }
                    //    }
                    //}
                }

                // A refuel plan at a point must be completed by refueling at the base (Commented)
                {
                    //for (int u = 1; u <= nUAVs; u++)
                    //{
                    //    // A point from where go for refueling
                    //    for (int p = 1; p < nPoints; p++)
                    //    {                        
                    //        List<BoolExpr> LExprs = new List<BoolExpr>();

                    //        int k = point_to_base_step[p];
                    //        if (point_to_base_step[p] <= 0)
                    //            continue;

                    //        for (int s = 1; s <= nTimeSteps - k; s++)
                    //        {
                    //            LExprs.Add(z3.MkImplies(UavRefuel[u, p, s], UavRefueling[u, s + k]));                            
                    //        }

                    //        for (int s = nTimeSteps - k + 1; s <= nTimeSteps; s++)
                    //        {
                    //            LExprs.Add(z3.MkNot(UavRefuel[u, p, s]));
                    //        }

                    //        slv.Assert(z3.MkAnd(LExprs));
                    //    }
                    //}
                }

                // Refueling at the base must be followed by a refuel plan at a point (needed to always have a value for UavRefueling) (Commented)            
                {
                    //for (int u = 1; u <= nUAVs; u++) // This part is only needed to always have a value for UavRefueling
                    //{
                    //    for (int s = 1; s <= nTimeSteps; s++)
                    //    {
                    //        List<BoolExpr> LExprs = new List<BoolExpr>();

                    //        // A point from where go for refueling
                    //        for (int p = 1; p < nPoints; p++)
                    //        {
                    //            int k = point_to_base_step[p];
                    //            if ((k <= 0) || (s - k <= 0))
                    //                continue;

                    //            LExprs.Add(UavRefuel[u, p, s - k]);
                    //        }

                    //        if (LExprs.Count > 0)
                    //            slv.Assert(z3.MkImplies(UavRefueling[u, s], z3.MkOr(LExprs)));
                    //    }
                    //}
                }

                // A returning to a point must follow a refueling at the base
                {
                    for (int u = 1; u <= nUAVs; u++)
                    {
                        // A point where to be returned for surveillance
                        for (int p = 1; p < nPoints; p++)
                        {
                            List<BoolExpr> LExprs = new List<BoolExpr>();

                            if (point_to_base_step[p] < 0)      // Those points are only considered from which the UAV can go to the base.
                                continue;                       // FIXED: It was "break" before

                            int k = 2 * point_to_base_step[p];

                            for (int s = 1; s <= k; s++)
                            {
                                LExprs.Add(z3.MkNot(UavReturn[u, p, s]));
                            }

                            for (int s = k + 1; s <= nTimeSteps; s++)
                            {
                                LExprs.Add(z3.MkImplies(UavReturn[u, p, s], UavRefuel[u, p, s - k]));
                            }

                            slv.Assert(z3.MkAnd(LExprs));
                        }
                    }
                }

                // The base is only visited when the UAV needs to refuel
                {
                    for (int u = 1; u <= nUAVs; u++)
                    {
                        //slv.Assert(z3.MkNot(UavPointVisit[u, nPoints, 1]));

                        for (int s = 2; s <= nTimeSteps; s++)
                        {
                            BoolExpr[] BExprs = new BoolExpr[nPoints - 1];

                            for (int p = 1; p < nPoints; p++)
                            {
                                BExprs[p - 1] = UavRefuel[u, p, s - 1];
                            }

                            slv.Assert(z3.MkImplies(UavPointVisit[u, nPoints, s], z3.MkOr(UavPointVisit[u, nPoints, s - 1], z3.MkOr(BExprs))));
                        }
                    }
                }
                #endregion

                #region Surveillance Score
                slv.Assert(z3.MkEq(SurveilledScore[0], ZeroR));

                for (int j = 1; j < nPoints; j++)
                {
                    slv.Assert(z3.MkImplies(Surveilled[j], z3.MkEq(SurveilledScore[j], z3.MkReal(point_weight[j]))));
                    slv.Assert(z3.MkImplies(z3.MkNot(Surveilled[j]), z3.MkEq(SurveilledScore[j], ZeroR)));
                }

                RealExpr ScoreSum = (RealExpr)z3.MkAdd(SurveilledScore);
                RealExpr ScoreDiv = (RealExpr)z3.MkDiv(ScoreSum, z3.MkReal(totalWeight));
                RealExpr NormalizedScore = (RealExpr)z3.MkMul(ScoreDiv, z3.MkReal(100));
                slv.Assert(z3.MkEq(TotalSurveillanceScore, NormalizedScore));

                slv.Assert(z3.MkGt(TotalSurveillanceScore, z3.MkReal(minSurveillanceScore)));
                #endregion

                #region Resilient Surveillance Score
                slv.Assert(z3.MkEq(ResSurveilledScore[0], ZeroR));

                for (int p = 1; p < nPoints; p++)
                {
                    slv.Assert(z3.MkImplies(ResSurveilled[p], z3.MkEq(ResSurveilledScore[p], z3.MkReal(point_weight[p]))));
                    slv.Assert(z3.MkImplies(z3.MkNot(ResSurveilled[p]), z3.MkEq(ResSurveilledScore[p], ZeroR)));
                }

                RealExpr ResScoreSum = (RealExpr)z3.MkAdd(ResSurveilledScore);
                //RealExpr NormalizedResScore = (RealExpr)z3.MkDiv(z3.MkMul(ResScoreSum, z3.MkReal(100)), z3.MkReal(totalWeight));                
                slv.Assert(z3.MkEq(TotalResSurveillanceScore, z3.MkDiv(z3.MkMul(ResScoreSum, z3.MkReal(100)), z3.MkReal(totalWeight))));

                slv.Assert(z3.MkGt(TotalResSurveillanceScore, z3.MkReal(minResSurveillanceScore)));
                #endregion

                #region Cyclic Trajectory (Commented)
                //// End placement of the UAVs (i.e., returns back to the starting position)
                //for (int u = 1; u <= nUAVs; u++)
                //{
                //    for (int p = 1; p <= nPoints; p++)
                //    {
                //        if (p == uav_init_position[u])
                //        {
                //            // If the UAV is alive
                //            slv.Assert(z3.MkImplies(Uav[u], UavPointVisit[u, p, nTimeSteps]));
                //            //slv.Assert(z3.MkImplies(z3.MkNot(Uav[u]), z3.MkNot(UavPointVisit[u, p, 1])));
                //        }
                //        //else // The following should be ensured by the other constraints 
                //        //{
                //        //    slv.Assert(z3.MkNot(UavPointVisit[u, p, 1]));
                //        //}
                //    }
                //}

                //// Remaining fuel at the end (which needs to be equal or greater than the initial fuel)
                //// The initial fule cannot be equal to the capacity (as after refueling/returning back for surveillance the remaining fuel is never the full)
                //for (int u = 1; u <= nUAVs; u++)
                //{
                //    BoolExpr BExpr = z3.MkImplies(Uav[u], z3.MkGe(UavFuelRem[u, nTimeSteps], z3.MkReal(uav_fuel_stored[u])));    // initial fuel given by input
                //    slv.Assert(BExpr);
                //}
                #endregion

                #region Alive UAVs (Minimize the Number of Live UAVs) (Commented)
                //{
                //    BoolExpr BExpr;                    

                //    for (int u = 1; u <= nUAVs; u++)
                //    {
                //        BExpr = z3.MkAnd(z3.MkImplies(Uav[u], z3.MkEq(UavInt[u], One)), z3.MkImplies(z3.MkNot(Uav[u]), z3.MkEq(UavInt[u], Zero)));
                //        slv.Assert(BExpr);
                //    }


                //    IntExpr[] IExprs = new IntExpr[nUAVs];

                //    for (int u = 1; u <= nUAVs; u++)
                //    {
                //        IExprs[u - 1] = UavInt[u];
                //    }

                //    slv.Assert(z3.MkEq(TotalUavAlive, z3.MkAdd(IExprs)));
                //    //slv.Assert(z3.MkEq(TotalUavAlive, z3.MkInt(7)));

                //    //slv.MkMinimize(TotalUavAlive);
                //}
                #endregion

                #region Solve the Model
                //tw.WriteLine();
                //tw.WriteLine("**************** Model ****************");
                //tw.Write(slv.ToString());
                //tw.WriteLine("***************************************");

                //slv.Push();

                // Resiliency Analysis: Failure of k UAVs
                int[] active_uav = new int[nUAVs + 1];

                for (int i = 1; i <= nUAVs; i++)
                {
                    active_uav[i] = 1;
                }

                //// Run for multiple way with k failed UAVs
                //long num_sol = nCr(nUAVs, nFailedUAVs);
                //Console.WriteLine("Number of run: " + num_sol);
                ////twResult.WriteLine("Number of run: " + num_sol);

                //for (int t = 1; t <= num_sol; t++)
                {
                    //slv.Pop();
                    //slv.Push();
                    //Random rnd = new Random(Guid.NewGuid().GetHashCode());

                    //// TODO: Need to generate all combinations. This random mechanism may miss some.
                    //for (int i = 1; i <= nFailedUAVs; i++)
                    //{
                    //    int m = rnd.Next(1, (nUAVs + 1));

                    //    while (active_uav[m] == 0)
                    //    {
                    //        m = rnd.Next(1, (nUAVs + 1));
                    //    }

                    //    active_uav[m] = 0;
                    //}

                    for (int v = 1; v <= nUAVs; v++)
                    {
                        if (active_uav[v] == 1)
                        {
                            slv.Assert(Uav[v]);
                            //Console.Write("{0}: Alive\t", v);
                            //twResult.Write("{0}: Alive\t", v);
                        }
                        else
                        {
                            slv.Assert(z3.MkNot(Uav[v]));
                            //Console.Write("{0}: Failed\t", v);
                            //twResult.Write("{0}: Failed\t", v);
                        }
                    }
                    //Console.WriteLine();
                    //twResult.WriteLine();
                    Enumerate();

                    //for (int a = 1; a <= nUAVs; a++)
                    //    active_uav[a] = 1;
                }

                //Enumerate();
                #endregion
            }
            catch (Z3Exception ex)
            {
                Console.WriteLine("Z3 Managed Exception: " + ex.Message);
                Console.WriteLine("Stack trace: " + ex.StackTrace);
            }
        }
        #endregion

        #region Enumerate
        void Enumerate()
        {
            Model model = null;

            DateTime start, end;
            // Write the premble to the files before execution
            {
                twResult = new StreamWriter("Surveillance_Result_v6.txt", true);
                twTime = new StreamWriter("Execution_Time_v6.txt", true);

                str = String.Format("Buses {0}, Lines {1}, UAVs {2}, and Time Units {3}: ", nBuses, nLines, nUAVs, nTimeSteps);
                twResult.WriteLine(str);
                twTime.WriteLine(str);
                Console.WriteLine(str);

                str = String.Format("Required Surveillance Time {0}, Resilient Visits {1}, and Resilient Surveillance Time {2} ",
                    visitTimeThres, visitResiliency, visitResTimeThres);
                twResult.WriteLine(str);
                twTime.WriteLine(str);
                Console.WriteLine(str);

                str = String.Format("Required Surveillance Score {0} and Resilient Surveillance Score {1} ",
                    minSurveillanceScore, minResSurveillanceScore);
                twResult.WriteLine(str);
                twTime.WriteLine(str);
                Console.WriteLine(str);

                start = DateTime.Now;
                str = String.Format("{0}: Start of Execution", start);
                twResult.WriteLine(str);
                twTime.WriteLine(str);
                Console.WriteLine(str);

                twTime.Close();
                twResult.Close();
            }

            Status st = slv.Check();

            // Write to the files after execution
            {
                end = DateTime.Now;
                str = String.Format("{0}: End of Execution (Execution Time: {1})", end, end.Subtract(start).TotalSeconds);
                Console.WriteLine(str);

                twResult = new StreamWriter("Surveillance_Result_v6.txt", true);
                twResult.WriteLine(str);
                twResult.Close();

                twTime = new StreamWriter("Execution_Time_v6.txt", true);
                twTime.WriteLine(str);
                twTime.Close();
            }

            // Write to the files according to the solver's outcome
            if (st == Status.SATISFIABLE)
            {
                model = slv.Model;

                twResult = new StreamWriter("Surveillance_Result_v6.txt", true);
                twUav = new StreamWriter("UAV_Point_" + NUM_BUS + "_Bus.txt", false);
                twUavPath = new StreamWriter("UAV_Path_v6.txt", true);
                twRefuel = new StreamWriter("Refuel_v6.txt", true);
                twTime = new StreamWriter("Execution_Time_v6.txt", true);
                twUavPath.WriteLine(nTimeSteps);


                #region UAV alive (Commented)
                twResult.WriteLine("Total UAVs in action: {0}", model.Eval(TotalUavAlive).ToString());

                str = String.Format("Alive UAVs: ");
                //Console..Write(str);
                twResult.Write(str);

                for (int u = 1; u <= nUAVs; u++)
                {
                    bool uavTrue = Convert.ToBoolean(model.Eval(Uav[u]).ToString());
                    if (uavTrue)
                    {
                        //Console..Write("{0} ", u);
                        twResult.Write("{0} ", u);
                    }
                }

                //Console..WriteLine();
                twResult.WriteLine();
                #endregion

                #region UAV visits
                str = String.Format("UAV visited points: ");
                //Console..WriteLine(str);
                twResult.WriteLine(str);
                for (int u = 1; u <= nUAVs; u++)
                {
                    str = String.Format("UAV {0} visits at: ", u);
                    //Console..Write(str);
                    twResult.Write(str);

                    bool flag = false;

                    for (int s = 1; s <= nTimeSteps; s++)
                    {
                        for (int p = 1; p <= nPoints; p++)
                        {
                            bool visitTrue = Convert.ToBoolean(model.Eval(UavPointVisit[u, p, s]).ToString());
                            if (visitTrue)
                            {
                                if (Convert.ToBoolean(model.Eval(UavRefuel[u, p, s]).ToString()))
                                {
                                    //Console..Write("({0}: Refueling Plan at {1}, {2}) ", s, p, model.Eval(UavFuelRem[u, s]).ToString());
                                    twResult.Write("{0}: Refueling Plan at {1}, {2}) ", s, p, model.Eval(UavFuelRem[u, s]).ToString());

                                    twRefuel.Write(p + " ");
                                }
                                else if (Convert.ToBoolean(model.Eval(UavReturn[u, p, s]).ToString()))
                                {
                                    //Console..Write("({0}:Returned at {1}, {2}) ", s, p, model.Eval(UavFuelRem[u, s]).ToString());
                                    twResult.Write("({0}:Returned at {1}, {2}) ", s, p, model.Eval(UavFuelRem[u, s]).ToString());

                                    flag = false;
                                }
                                else if (p == nPoints)
                                {
                                    if (Convert.ToBoolean(model.Eval(UavRefueling[u, s]).ToString()))
                                    {
                                        //Console..Write("({0}: Refueling at the Base, {1}) ", s, model.Eval(UavFuelRem[u, s]).ToString());
                                        twResult.Write("({0}: Refueling at the Base, {1}) ", s, model.Eval(UavFuelRem[u, s]).ToString());

                                        ////Console..Write("({0}: Returning Plan to {1}, {2}) ", s, model.Eval(UavReturning[u, s]).ToString(), model.Eval(UavFuelRem[u, s]).ToString());
                                        //twResult.Write("({0}: Returning Plan to {1}, {2}) ", s, model.Eval(UavReturning[u, s]).ToString(), model.Eval(UavFuelRem[u, s]).ToString());

                                        flag = true;
                                    }
                                    else if (flag)
                                    {
                                        //Console..Write("({0}: From the Base, {1}) ", s, model.Eval(UavFuelRem[u, s]).ToString());
                                        twResult.Write("({0}: From the Base, {1}) ", s, model.Eval(UavFuelRem[u, s]).ToString());
                                    }
                                    else
                                    {
                                        //Console..Write("({0}: To the Base, {1}) ", s, model.Eval(UavFuelRem[u, s]).ToString());
                                        twResult.Write("({0}: To the Base, {1}) ", s, model.Eval(UavFuelRem[u, s]).ToString());
                                    }
                                }
                                else
                                {
                                    //Console..Write("({0}: {1}, {2}) ", s, p, model.Eval(UavFuelRem[u, s]).ToString());
                                    twResult.Write("({0}: {1}, {2}) ", s, p, model.Eval(UavFuelRem[u, s]).ToString());

                                    twUav.Write(p + " ");
                                    twUavPath.Write(p + " ");
                                }
                            }
                        }
                    }

                    //Console..WriteLine();
                    twUav.WriteLine();

                    twRefuel.WriteLine();
                    twUavPath.WriteLine();

                    twResult.WriteLine();
                    twResult.WriteLine();
                }
                #endregion                

                #region The points that are covered
                str = String.Format("Surveilled Points: ");
                //Console..Write(str);
                twResult.Write(str);
                for (int p = 1; p < nPoints; p++)
                {
                    bool coverTrue = Convert.ToBoolean(model.Eval(Surveilled[p]).ToString());
                    if (coverTrue)
                    {
                        //Console..Write("{0} ", p);
                        twResult.Write("{0} ", p);
                    }
                }

                //Console..WriteLine();
                twResult.WriteLine();

                str = String.Format("Resilient Surveilled Points: ");
                //Console..Write(str);
                twResult.Write(str);
                for (int p = 1; p < nPoints; p++)
                {
                    bool coverTrue = Convert.ToBoolean(model.Eval(ResSurveilled[p]).ToString());
                    if (coverTrue)
                    {
                        //Console..Write("{0} ", p);
                        twResult.Write("{0} ", p);
                    }
                }

                //Console..WriteLine();
                twResult.WriteLine();

                for (int p = 1; p <= nPoints; p++)
                {
                    str = String.Format("Point {0} was visited [at, by]: ", p);

                    //Console..Write(str);
                    twResult.Write(str);
                    for (int s = 1; s <= nTimeSteps; s++)
                    {
                        for (int u = 1; u <= nUAVs; u++)
                        {
                            bool visitTrue = Convert.ToBoolean(model.Eval(UavPointVisit[u, p, s]).ToString());
                            if (visitTrue)
                            {
                                //Console..Write("[{0}, {1}] ", s, u);
                                twResult.Write("[{0}, {1}] ", s, u);
                            }
                        }
                    }

                    //Console..WriteLine();
                    twResult.WriteLine();
                }
                #endregion                                

                #region Remaining fuel (Commented)
                //for (int u = 1; u <= nUAVs; u++)
                //{
                //    str = String.Format("Remaining Fuel for UAV {0}: ", u);
                //    twResult.WriteLine(str);
                //    Console.WriteLine(str);

                //    for (int s = 1; s <= nTimeSteps; s++)
                //    {
                //        string res = model.Eval(UavFuelRem[u, s]).ToString();

                //        twResult.Write("{0} ", res);
                //        Console.Write("{0} ", res);
                //    }
                //    Console.WriteLine();
                //    twResult.WriteLine();
                //}
                #endregion

                #region surveillance score solver
                twResult.WriteLine("Surveillance Score: " + ToDouble(model.Eval(TotalSurveillanceScore).ToString()) + "%");
                twTime.WriteLine("Surveillance Score: " + ToDouble(model.Eval(TotalSurveillanceScore).ToString()) + "%");

                //Console..WriteLine("Surveillance Score: " + ToDouble(model.Eval(TotalSurveillanceScore).ToString()) + "%");

                twResult.WriteLine("Resileint Surveillance Score: " + ToDouble(model.Eval(TotalResSurveillanceScore).ToString()) + "%");
                twTime.WriteLine("Resileint Surveillance Score: " + ToDouble(model.Eval(TotalResSurveillanceScore).ToString()) + "%");
                //Console..WriteLine("Resilient Surveillance Score: " + ToDouble(model.Eval(TotalResSurveillanceScore).ToString()) + "%");
                #endregion

                model.Dispose();

                twUavPath.WriteLine();
                twUavPath.Close();
                twUav.Close();
                twRefuel.Close();

                twResult.Close();
                twTime.Close();
            }
            else
            {
                //Console.WriteLine(slv.UnsatCore);
                Console.WriteLine("We have no solution");

                //tw = new StreamWriter("Output.txt", false);
                //tw.WriteLine("We have no solution");
                //tw.Close();

                twResult = new StreamWriter("Surveillance_Result_v6.txt", true);
                twResult.WriteLine("We have no solution");
                twResult.Close();

                twTime = new StreamWriter("Execution_Time_v6.txt", true);
                twTime.WriteLine("We have no solution");
                twTime.Close();
            }
        }
        #endregion

        #region Model
        void Model()
        {
            Console.Write("Z3 Major Version: ");
            Console.WriteLine(Microsoft.Z3.Version.Major.ToString());
            Console.Write("Z3 Full Version: ");
            Console.WriteLine(Microsoft.Z3.Version.ToString());
            Console.WriteLine();

            Dictionary<string, string> cfg = new Dictionary<string, string>() {
                    { "MODEL", "true"},
                    { "TIMEOUT", MAX_EXEC_TIME}
                };


            try
            {
                //Global.SetParameter("SMT.ARITH.RANDOM_INITIAL_VALUE", "true");
                //Global.SetParameter("SMT.RANDOM_SEED", "6");
                //Global.SetParameter("PP.DECIMAL", "true");

                z3 = new Context(cfg);
                slv = z3.MkSolver();
                //slv = z3.MkOptimize();

                #region Tactics
                Tactic T_NRA = z3.MkTactic("nra");      // Non-linear Real Arithmetic // The best so far.
                //Tactic T_LRA = z3.MkTactic("lra");    // Linear Real Arithmetic (NOT suitable at all as the model has multiplicaitons of two unknowns)

                //Tactic T_SMT = z3.MkTactic("sat");    // Including "smt", not working well
                Tactic T_SIMP = z3.MkTactic("simplify");
                Tactic T_SPLIT = z3.MkTactic("split-clause");     // Split-clause is not helping as it was expected


                Params P = z3.MkParams();
                P.Add("random_seed", 0);

                //Params P1 = z3.MkParams();
                //P1.Add("random_seed", 5);

                Params P2 = z3.MkParams();
                P2.Add("random_seed", 7);

                //Tactic T_GOAL = z3.AndThen(T_SIMP, z3.ParAndThen(T_SPLIT, T_NRA));
                Tactic T_GOAL = z3.AndThen(z3.Repeat(T_SIMP), z3.ParAndThen(T_SPLIT, z3.ParOr(T_NRA, z3.With(T_NRA, P2))));   // Working well

                //Tactic T_GOAL = z3.AndThen(T_SIMP, z3.AndThen(T_SPLIT, z3.ParOr(z3.With(T_NRA, P), z3.With(T_NRA, P2))));
                //Tactic T_GOAL = z3.AndThen(T_SIMP, z3.ParOr(z3.With(T_NRA, P), z3.With(T_NRA, P2), z3.With(T_LRA, P), z3.With(T_LRA, P2)));

                //// Multiple parallel runs are NOT also helping (CAN be running the both/all on the same machine)
                //Tactic T_GOAL = z3.AndThen(T_SIMP, z3.ParOr(z3.With(T_NRA, P), z3.With(T_NRA, P2))); 

                //Tactic T_GOAL = z3.AndThen(T_SIMP, T_NRA);      // The best so far.
                //twResult.WriteLine("z3.AndThen(T_SIMP, T_NRA)");

                //Tactic T_GOAL = z3.AndThen(T_SIMP, T_SMT);

                //slv = z3.MkSolver(T_GOAL);
                //twTime = new StreamWriter("Execution_Time_v6.txt", true);
                //str = String.Format("T_Goal", T_GOAL.ToString());                
                //twTime.WriteLine(str);
                //twTime.Close();
                #endregion

                ReadInput();
                Initialize();
                Formalize();
                //Enumerate();
            }
            catch (Z3Exception ex)
            {
                Console.WriteLine("Z3 Managed Exception: " + ex.Message);
                Console.WriteLine("Stack trace: " + ex.StackTrace);
            }
            catch (Exception ex)
            {
                Console.WriteLine("Exception: " + ex.Message);
                Console.WriteLine("Stack trace: " + ex.StackTrace);
            }
        }
        #endregion

        static void Main(string[] args)
        {
            //tw = new StreamWriter("Output.txt", false);            			         

            string ExecutingFile = new System.Diagnostics.StackTrace(true).GetFrame(0).GetFileName();

            twResult = new StreamWriter("Surveillance_Result_v6.txt", true);
            twTime = new StreamWriter("Execution_Time_v6.txt", true);

            twResult.WriteLine("Executing " + ExecutingFile + " ...........");
            twTime.WriteLine("Executing " + ExecutingFile + " ...........");

            twResult.Close();
            twTime.Close();

            Stopwatch stopWatch = new Stopwatch();

            stopWatch.Start();
            UavSurveillance uIn = new UavSurveillance();
            uIn.Model();
            //Console..WriteLine("Program ends");
            stopWatch.Stop();

            Console.WriteLine("Total Required time: {0}", stopWatch.Elapsed.TotalSeconds);

            twResult = new StreamWriter("Surveillance_Result_v6.txt", true);
            twResult.WriteLine("Total Required time: {0}", stopWatch.Elapsed.TotalSeconds);
            twResult.WriteLine("***********************************");
            twResult.WriteLine();
            twResult.Close();

            twTime = new StreamWriter("Execution_Time_v6.txt", true);
            twTime.WriteLine("Total Required time: {0}", stopWatch.Elapsed.TotalSeconds);
            twTime.WriteLine();
            twTime.Close();

            //tw.Close();
        }
    }
}