using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;


namespace SCOPF
{
    class CaOpf
    {
        Context z3;       
        Optimize opt;

        static TextWriter tw;

      
        #region constant
        const int NBUSES = 5;
        const int NLINES = 7;
        const int STEPS = 50;
        const int THRESHOLD_DIFF = 5;   // Generation power can be little over than the actual demand (In Percent)
        const double THRESHOLD_THETA_DIFF = 0.35;  // Generation power can be little over than the In Percent
        //const int LINE_K = 4;
        //const double MIN_CH = -0.5;
        //const double MAX_CH = 0.5;
        const double TOTAL_OVERLOAD_CONTINGENCY = 6;

        #endregion

        #region input variables
        int nBuses, nLines, nMeasurements, nDBuses, nGBuses, nOverloads;  // nBuses also represents the number of states               

        bool[] mBD, mBG;        // mBG for whether a bus has a generator // mBD for whether a bus has a load        

        int[,] connected, powerLine, mConnect;
        double[] lineAdmittance;
        double[] flow_overload_limit;

        int refBus;
        double[,] costCoef;
        double[,] LODF;
        double[,] SHIFT_FACTOR;
        //double[] changed_demand;
       
        double maxGenCost;

        double[] demand, maxBPD, minBPD, maxBPG, minBPG, maxPL;
        double[] stepChangeBPG;

        //double minLdCh;
        double minLineOverload;
        #endregion

        #region z3 variables
        RealExpr[] BPD, BPG;
        // Original demand and generation
        // We may take an arbitrary demand within the range

        RealExpr[] Attack_Load; // new load for attack
        RealExpr[] Delta_Load;
        RealExpr[] FLP, BLP, BP, Theta;
        RealExpr[] REAL_BP;
        
        RealExpr TBPD, TBPG, ThCostPG, Cost, TotalAttackLoad, TotalDeltaLoad;
        IntExpr[] BoundPre;
        //IntExpr a, b;

        RealExpr[] CA_FLP;
        RealExpr[,] Lines_Contingency_Flow;
        RealExpr[,] Back_Lines_Contingency_Flow;
        RealExpr[] SF_Flow;
        RealExpr[] Back_SF_Flow;
        RealExpr[,] SF_Lines_Contingency_Flow;
        RealExpr[,] SF_Back_Lines_Contingency_Flow;

        BoolExpr[] IsOverFlow;
        IntExpr[] OverLineCount;

        BoolExpr[,] IsOverFlowContgn;
        IntExpr[] OverLineCountContgn;
        //RealExpr[] OverFlow;
        #endregion


        #region Z3 Initialization
        void Declaration(Context z3)
        {
            int i;
            String str;

            #region Related to Optimal Power Flow
            //BD = new BoolExpr[nBuses + 1];
            //for (i = 1; i <= nBuses; i++)
            //{
            //    BD[i] = (BoolExpr)z3.MkConst("BD_" + i, z3.BoolSort);
            //}

            //BG = new BoolExpr[nBuses + 1];
            //for (i = 1; i <= nBuses; i++)
            //{
            //    BG[i] = (BoolExpr)z3.MkConst("BG_" + i, z3.BoolSort);
            //}

            BPD = new RealExpr[nBuses + 1];
            Attack_Load = new RealExpr[nBuses + 1];
            Delta_Load = new RealExpr[nBuses + 1];
            for (i = 0; i <= nBuses; i++)
            {
                BPD[i] = (RealExpr)z3.MkConst("BPDemand_" + i, z3.RealSort);
                Attack_Load[i] = (RealExpr)z3.MkConst("ChangedDemand_" + i, z3.RealSort);
                Delta_Load[i] = (RealExpr)z3.MkConst("DeltaLoad" + i, z3.RealSort);
            }

            BPG = new RealExpr[nBuses + 1];
            for (i = 0; i <= nBuses; i++)
            {
                BPG[i] = (RealExpr)z3.MkConst("BPGeneration_" + i, z3.RealSort);
            }

            FLP = new RealExpr[nLines + 1];
            CA_FLP = new RealExpr[nLines + 1];
            SF_Flow = new RealExpr[nLines + 1];
            Back_SF_Flow = new RealExpr[nLines + 1];
            IsOverFlow = new BoolExpr[nLines + 1];
            OverLineCount = new IntExpr[nLines+1];

            IsOverFlowContgn = new BoolExpr[nLines + 1, nLines + 1];
            OverLineCountContgn = new IntExpr[nLines + 1];
            for (i = 0; i <= nLines; i++)
            {
                FLP[i] = (RealExpr)z3.MkConst("FLPower_" + i, z3.RealSort);
                CA_FLP[i]= (RealExpr)z3.MkConst("CA_FLPower_" + i, z3.RealSort);
                SF_Flow[i] = (RealExpr)z3.MkConst("SF_Flow_" + i, z3.RealSort);
                Back_SF_Flow[i] = (RealExpr)z3.MkConst("Back_SF_Flow_" + i, z3.RealSort);
                IsOverFlow[i] = (BoolExpr)z3.MkConst("IsOverFlow_" + i, z3.BoolSort);
                OverLineCount[i] = (IntExpr)z3.MkConst("OverFlow_" + i, z3.IntSort);               
                OverLineCountContgn[i] = (IntExpr)z3.MkConst("OverFlowContingency_" + i, z3.IntSort);
            }

            Lines_Contingency_Flow = new RealExpr[nLines + 1, nLines + 1];
            Back_Lines_Contingency_Flow = new RealExpr[nLines + 1, nLines + 1];
            SF_Lines_Contingency_Flow = new RealExpr[nLines + 1, nLines + 1];
            SF_Back_Lines_Contingency_Flow = new RealExpr[nLines + 1, nLines + 1];
            for (i=0; i<=nLines; i++)
            {
                for(int j=0; j<= nLines; j++)
                {
                    str = String.Format("PowerFlow_{0}_{1}", i,j);                  
                    Lines_Contingency_Flow[i,j] = (RealExpr)z3.MkConst(str, z3.RealSort);
                    str = String.Format("Back_PowerFlow_{0}_{1}", i, j);
                    Back_Lines_Contingency_Flow[i, j] = (RealExpr)z3.MkConst(str, z3.RealSort);
                    str = String.Format("SF_PowerFlow_{0}_{1}", i, j);
                    SF_Lines_Contingency_Flow[i, j] = (RealExpr)z3.MkConst(str, z3.RealSort);
                    str = String.Format("SF_Back_PowerFlow_{0}_{1}", i, j);
                    SF_Back_Lines_Contingency_Flow[i, j] = (RealExpr)z3.MkConst(str, z3.RealSort);
                    str = String.Format("IsOverFlowContingency_{0}_{1}", i, j);
                    IsOverFlowContgn[i, j] = (BoolExpr)z3.MkConst(str, z3.BoolSort);
                }
            }

            BLP = new RealExpr[nLines + 1];
            for (i = 0; i <= nLines; i++)
            {
                BLP[i] = (RealExpr)z3.MkConst("BLPower_" + i, z3.RealSort);
            }

            BP = new RealExpr[nBuses + 1];
            for (i = 0; i <= nBuses; i++)
            {
                BP[i] = (RealExpr)z3.MkConst("BPower_" + i, z3.RealSort);
            }

            Theta = new RealExpr[nBuses + 1];
            for (i = 0; i <= nBuses; i++)
            {
                Theta[i] = (RealExpr)z3.MkConst("Theta_" + i, z3.RealSort);
            }

            REAL_BP = new RealExpr[nBuses + 1];
            for (i = 0; i <= nBuses; i++)
            {
                REAL_BP[i] = (RealExpr)z3.MkConst("RealBPower_" + i, z3.RealSort);
            }


            TBPD = (RealExpr)z3.MkConst("TotalBPD", z3.RealSort);
            TBPG = (RealExpr)z3.MkConst("TotalBPD", z3.RealSort);
            TotalAttackLoad = (RealExpr)z3.MkConst("TotalAttackLoad", z3.RealSort);
            TotalDeltaLoad = (RealExpr)z3.MkConst("TotalDeltaLoad", z3.RealSort);
            //TCostPG = (RealExpr)z3.MkConst("TotalCostPG", z3.RealSort);
            ThCostPG = (RealExpr)z3.MkConst("THCostGen", z3.RealSort);
            Cost = (RealExpr)z3.MkConst("Final SCOPF Cost", z3.RealSort);
            BoundPre = new IntExpr[nBuses + 1];
            for (i = 0; i <= nBuses; i++)
            {
                BoundPre[i] = (IntExpr)z3.MkConst("BoundPre_" + i, z3.IntSort);
            }
            #endregion
        }


        #endregion

        #region utility Function
        double ToDouble(String doubleString)
        {
            double val = 0.0;
            bool negSign = false;
            String[] parts;

            if (doubleString[0] == '-')
                negSign = true;

            char[] delims = { '-', '/', ' ' };

            parts = doubleString.Split(delims, StringSplitOptions.RemoveEmptyEntries);
            if (parts.Length != 2)
            {
                if (parts.Length == 1)
                {
                    if (parts[0].Equals("0"))
                        return 0;
                }

                Console.WriteLine("ToDouble: Exit due to Wrong Input Format");
                Environment.Exit(0);
            }

            int numDigists, maxDigits = 16;
            if (parts[0].Length > maxDigits || parts[1].Length > maxDigits)
            {
                if (parts[0].Length > parts[1].Length)
                {
                    numDigists = parts[0].Length;
                    parts[1] = parts[1].PadLeft(numDigists, '0');
                }
                else if (parts[0].Length < parts[1].Length)
                {
                    numDigists = parts[1].Length;
                    parts[0] = parts[0].PadLeft(numDigists, '0');
                }
                else
                    numDigists = parts[0].Length;

                parts[0] = parts[0].Remove(numDigists - maxDigits + 1);
                parts[1] = parts[1].Remove(numDigists - maxDigits + 1);
            }

            double part0 = Convert.ToDouble(parts[0]);
            double part1 = Convert.ToDouble(parts[1]);

            val = part0 / part1;

            if (negSign)
                return -val;
            else
                return val;
        }

        #endregion

        #region input from file
        void ReadInput(Context z3, Optimize o)
        {
            String line;
            String[] lineElement;

            int i, j;
            Random rand = new Random();

            try
            {
                System.IO.StreamReader file = new System.IO.StreamReader(String.Format("input_scopf_{0}_{1}.txt", NBUSES, NLINES));
                //System.IO.StreamReader file = new System.IO.StreamReader(String.Format("input_2_scopf_5_7.txt"));

                System.IO.StreamReader lodf_file = new System.IO.StreamReader(String.Format("input_LODF_{0}_{1}.txt", NBUSES, NLINES));

                System.IO.StreamReader sf_file = new System.IO.StreamReader(String.Format("input_SF_{0}_{1}.txt", NBUSES, NLINES));

                //System.IO.StreamReader changed_load_file = new System.IO.StreamReader(String.Format("input_CHLoad_{0}_{1}.txt", NBUSES, NLINES));

                char[] delims = { ' ', ',', '\t' };

                #region Number of buses, lines, the reference bus and Number of overload lines
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 4)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    nBuses = Convert.ToInt32(lineElement[0]);
                    nLines = Convert.ToInt32(lineElement[1]);
                    refBus = Convert.ToInt32(lineElement[2]);
                    nOverloads = Convert.ToInt32(lineElement[3]);
                    Console.WriteLine("buses: {0} | lines: {1} | overloaded lines: {2}", nBuses ,nLines, nOverloads);

                    nMeasurements = 2 * nLines + nBuses;
                    Console.WriteLine("measurements: {0}", nMeasurements);                  

                    break;
                }
                #endregion

                #region Initializations
                {
                    Declaration(z3);

                    mBD = new bool[nBuses + 1];
                    mBG = new bool[nBuses + 1];
                    

                    powerLine = new int[nLines + 1, 2];  // The first two entries are for the end buses.
                    lineAdmittance = new double[nLines + 1];
                    connected = new int[nLines + 1, nLines + 1];
                    flow_overload_limit = new double[nLines + 1];

                    // A bus is connected with which bus. First element is the number of connected buses.
                    mConnect = new int[nBuses + 1, nBuses + 1];
                    for (i = 1; i <= nBuses; i++)
                        for (j = 1; j <= nBuses; j++)
                            mConnect[i, j] = 0;

                    demand = new double[nBuses + 1];

                    //changed_demand = new double[nBuses + 1];

                    maxPL = new double[nLines + 1];
                    minBPD = new double[nBuses + 1];
                    maxBPD = new double[nBuses + 1];
                    minBPG = new double[nBuses + 1];
                    maxBPG = new double[nBuses + 1];                    

                    costCoef = new double[nBuses + 1, 2];
                    stepChangeBPG = new double[nBuses + 1];

                    LODF = new double[nLines, nLines];
                    SHIFT_FACTOR = new double[nLines, nBuses]; // actual size (bus-1) due to reference bus
                    
                }
                #endregion

                #region Line properties
                {
                    int from, to;
                    double impd, flowLim;

                    i = 1;  // Number of line
                    while (i <= nLines)
                    {
                        if ((line = file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input (Line properties)");
                            Environment.Exit(0);
                        }
                        line = line.Trim();
                        //Console.WriteLine(line);
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;
                        
                        lineElement = line.Split(delims);
                        //Console.WriteLine(lineElement.Length);
                        if (lineElement.Length != 5)
                        {
                            //Console.WriteLine("entered");
                            Console.WriteLine("Exit due to Wrong Number of Input.........Line properties");
                            Environment.Exit(0);
                        }

                        //k = Convert.ToInt32(words[0]);  // Line No, what we assume equal to i
                        from = Convert.ToInt32(lineElement[1]);
                        to = Convert.ToInt32(lineElement[2]);
                        impd = Convert.ToDouble(lineElement[3]);
                        flowLim = Convert.ToDouble(lineElement[4]);

                        powerLine[i, 0] = from;
                        powerLine[i, 1] = to;
                        lineAdmittance[i] = impd;
                        maxPL[i] = flowLim;

                        mConnect[from, to] = mConnect[to, from] = i;

                        if ((from != 0) && (to != 0))
                        {
                            connected[from, 0]++;
                            connected[from, connected[from, 0]] = to;
                            connected[to, 0]++;
                            connected[to, connected[to, 0]] = from;
                        }

                        i++;
                    }
                }
                #endregion                
                
                #region Generation and load bus
                {
                    nGBuses = 0;
                    nDBuses = 0;

                    i = 1;  // Bus No        
                    bool bBLoad, bBGen;
                    while (i <= nBuses)
                    {
                        if ((line = file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input");
                            Environment.Exit(0);
                        }

                        line = line.Trim();
                        //Console.Write(line.Length + " ");
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;

                        lineElement = line.Split(delims);
                        //Console.Write(lineElement.Length + " ");
                        if (lineElement.Length != 3)
                        {
                            Console.WriteLine("Exit due to Wrong Number of Input (BUS/LOAD)");
                            Environment.Exit(0);
                        }

                        //k = Convert.ToInt32(words[0]);  // Measurement No, what we assume equal to i
                        bBGen = Convert.ToBoolean(Convert.ToInt32(lineElement[1]));
                        bBLoad = Convert.ToBoolean(Convert.ToInt32(lineElement[2]));

                        if (bBGen)
                        {
                            //s.Assert(BG[i]);
                            mBG[i] = true;
                            nGBuses++;
                        }
                        else
                            mBG[i] = false;
                        //s.Assert(z3.MkNot(BG[i]));


                        if (bBLoad)
                        {
                            //s.Assert(BD[i]);
                            mBD[i] = true;
                            nDBuses++;
                        }
                        else
                            mBD[i] = false;
                        //s.Assert(z3.MkNot(BD[i]));

                        i++;
                    }

                    int k;  // Bus No

                    // Generation buses                                        
                    if (nGBuses > 0)
                    {
                        for (i = 1; i <= nGBuses; i++)
                        {
                            while (true)
                            {
                                if ((line = file.ReadLine()) == null)
                                {
                                    Console.WriteLine("Exit due to Insufficient Input");
                                    Environment.Exit(0);
                                }

                                line = line.Trim();
                                if ((line.Length == 0) || line.StartsWith("#"))
                                    continue;

                                lineElement = line.Split(delims);
                                if (lineElement.Length != 5)
                                {
                                    Console.WriteLine("Exit due to Wrong Number of Input");
                                    Environment.Exit(0);
                                }

                                k = Convert.ToInt32(lineElement[0]);
                                maxBPG[k] = Convert.ToDouble(lineElement[1]);
                                minBPG[k] = Convert.ToDouble(lineElement[2]);
                                costCoef[k, 0] = Convert.ToDouble(lineElement[3]);
                                costCoef[k, 1] = Convert.ToDouble(lineElement[4]);

                                stepChangeBPG[k] = (maxBPG[k] - minBPG[k]) / STEPS;
                                break;
                            }
                        }
                    }

                    // Load buses
                    if (nDBuses > 0)
                    {
                        for (i = 1; i <= nDBuses; i++)
                        {
                            while (true)
                            {
                                if ((line = file.ReadLine()) == null)
                                {
                                    Console.WriteLine("Exit due to Insufficient Input");
                                    Environment.Exit(0);
                                }

                                line = line.Trim();
                                if ((line.Length == 0) || line.StartsWith("#"))
                                    continue;

                                lineElement = line.Split(delims);
                                if (lineElement.Length != 4)
                                {
                                    Console.WriteLine("Exit due to Wrong Number of Input");
                                    Environment.Exit(0);
                                }

                                k = Convert.ToInt32(lineElement[0]);
                                demand[k] = Convert.ToDouble(lineElement[1]);
                                maxBPD[k] = Convert.ToDouble(lineElement[2]);
                                minBPD[k] = Convert.ToDouble(lineElement[3]);
                               // changed_demand[k] = Convert.ToDouble(lineElement[4]); // Why is the last element
                                break;
                            }
                        }
                    }
                }
                #endregion

                #region Cost Constraint
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 1)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    maxGenCost = Convert.ToDouble(lineElement[0]);
                    Console.WriteLine("max generation cost: {0}" , maxGenCost);
                    tw.WriteLine("max generation cost: {0}", maxGenCost, "%");
                    o.Assert(z3.MkEq(ThCostPG, z3.MkReal(Convert.ToString(maxGenCost))));                    

                    break;
                }
                #endregion

                #region LINE OVERLOAD AMOUNT
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 1)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    minLineOverload = Convert.ToDouble(lineElement[0]);
                    Console.WriteLine("max overloading: {0}", minLineOverload);
                    tw.WriteLine("max overloading: {0}", minLineOverload);                    

                    break;
                }
                #endregion

                /*
                #region Old LINE OVERLOAD AMOUNT (We do not need them, Commented now)
                
                i = 1;
                while (i <= nLines)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input (LINE OVERLOAD minimum)");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    // Console.WriteLine(lineElement[0]);
                    //Console.WriteLine(lineElement.Length);
                    if (lineElement.Length != 2)
                    {
                        Console.WriteLine("entered");
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    //k = Convert.ToInt32(lineElement[0]);  // Line No, what we assume equal to i
                    flow_overload_limit[i] = Convert.ToDouble(lineElement[1]);
                    i++;

                }
                
                #endregion
                */
                file.Close();

                
                #region input LODF matrix

                for (int l = 0; l < nLines; l++)
                {
                    while (true)
                    {
                        if ((line = lodf_file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input");
                            Environment.Exit(0);
                        }

                        line = line.Trim();
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;

                        lineElement = line.Split(delims);
                        if (lineElement.Length != nLines)
                        {
                            Console.WriteLine("Exit due to Wrong Number of Input");
                            Environment.Exit(0);
                        }

                        for(int k=0;k<lineElement.Length; k++)
                        {
                            LODF[l, k] = Convert.ToDouble(lineElement[k]);
                        }

                        break;
                    }
                }
                              

                #endregion

                lodf_file.Close();


                #region input SF matrix

                for (int l = 0; l < nLines; l++)
                {
                    while (true)
                    {
                        if ((line = sf_file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input");
                            Environment.Exit(0);
                        }

                        line = line.Trim();
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;

                        lineElement = line.Split(delims);
                        //if (lineElement.Length != nLines)
                        //{
                        //    Console.WriteLine("Exit due to Wrong Number of Input");
                        //    Environment.Exit(0);
                        //}

                        for (int k = 0; k < lineElement.Length; k++)
                        {
                            SHIFT_FACTOR[l, k+1] = Convert.ToDouble(lineElement[k]);
                        }

                        break;
                    }
                }

                #endregion

                sf_file.Close();
            }
            catch (Exception e)
            {
                throw e;
            }
            
            

            Console.WriteLine("\nLODF Input");
            for (int l = 0; l < nLines; l++)
            {
                for (int k = 0; k < nLines; k++)
                {
                    Console.Write(LODF[l, k]+" ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();


            Console.WriteLine("\nSHIFT FACTOR Input");
            for (int l = 0; l < nLines; l++)
            {
                for (int k = 0; k < nBuses; k++)
                {
                    Console.Write(SHIFT_FACTOR[l, k] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();


            //Console.WriteLine("\nChanged LOAD Input");
            //for (int l = 0; l < nLines; l++)
            //{
            //    Console.WriteLine(changed_demand[l] + " ");               
            //}
            //Console.WriteLine();

        
        }

        #endregion

               
        #region Formalization
        void Formalize(Context z3, Optimize opt)
        {
            RealExpr Zero = z3.MkReal(0);
            RealExpr One = z3.MkReal(1);

            #region BUS REAL LOAD
            {
                BoolExpr[] Exprs = new BoolExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    if (mBD[j])
                        Exprs[j - 1] = z3.MkEq(BPD[j], z3.MkReal(Convert.ToString(demand[j])));
                    else
                        Exprs[j - 1] = z3.MkEq(BPD[j], Zero);
                }

                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
            }

            {
                RealExpr[] Exprs = new RealExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    Exprs[j - 1] = BPD[j];
                }

                BoolExpr Expr = z3.MkEq(TBPD, z3.MkAdd(Exprs));
                opt.Assert(Expr);
            }

            ////REAL Load in LIMIT or NOT ??? // We do not need it here. We need it when we consider the change in load.
            //{
            //    BoolExpr[] Exprs = new BoolExpr[nBuses];
            //    for (int j = 1; j <= nBuses; j++)
            //    {

            //        Exprs[j - 1] = z3.MkAnd(z3.MkGe(BPD[j], z3.MkReal(Convert.ToString(minBPD[j]))),
            //            z3.MkLe(BPD[j], z3.MkReal(Convert.ToString(maxBPD[j]))));
            //    }

            //    BoolExpr Expr = z3.MkAnd(Exprs);
            //    opt.Assert(Expr);
            //}

            #endregion

            //////////////////////// SCOPF /////////////////////////
            #region SCOPF

            #region ATTACKED/CHANGED LOAD  (COMMENTED, we dont need this) 
            // Attacked LOAD calculation (Commented, we don't need that)
            {
                /*
                BoolExpr[] Exprs = new BoolExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    if (mBD[j])
                    {
                        Exprs[j - 1] = z3.MkEq(Attack_Load[j], BPD[j]);
                        //Exprs[j - 1] = z3.MkEq(Attack_Load[j], z3.MkAdd(BPD[j], z3.MkReal(Convert.ToString(0.5))));
                    }                        
                    else
                    {
                        Exprs[j - 1] = z3.MkEq(Attack_Load[j], Zero);
                    }
                        
                }
                BoolExpr Expr = z3.MkAnd(Exprs);
               // opt.Assert(Expr);
               */
            }

            // MAX/MIN LIMIT of load (Commented, we don't need that)
            {
                /*
                BoolExpr[] Exprs = new BoolExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    Exprs[j - 1] = z3.MkAnd(z3.MkGe(BPD[j], z3.MkReal(Convert.ToString(minBPD[j]))),
                        z3.MkLe(BPD[j], z3.MkReal(Convert.ToString(maxBPD[j]))));                    
                }
                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
                */
            }

            // SUM of all DELTA_LOAD must be ZERO (Commented, we don't need that)
            {
                /*
                RealExpr[] Exprs = new RealExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                   // Exprs[j - 1] = (RealExpr) z3.MkSub(Attack_Load[j],BPD[j]);
                    Exprs[j - 1] = Delta_Load[j];
                }
                BoolExpr Expr = z3.MkAnd(z3.MkGe(z3.MkAdd(Exprs), z3.MkReal(Convert.ToString(-0.0000000001))),
                    z3.MkLe(z3.MkAdd(Exprs), z3.MkReal(Convert.ToString(0.0000000001))));
                //opt.Assert(Expr);     
                */
            }

            // SUM OF ATTACKED_LOAD (Commented, we don't need that)
            {
                /*
                RealExpr[] Exprs = new RealExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    Exprs[j - 1] = BPD[j];
                }
                BoolExpr Expr = z3.MkEq(TotalAttackLoad, z3.MkAdd(Exprs));
                //opt.Assert(Expr);
                */
            }
            #endregion

            #region Sum of ATTACK LOAD = Sum of GENERATION
            {
                RealExpr[] Exprs = new RealExpr[nGBuses];
                int k = 0;
                for (int j = 1; j <= nBuses; j++)
                {
                    if (mBG[j])
                        Exprs[k++] = BPG[j];
                }

                opt.Assert(z3.MkEq(TBPG, z3.MkAdd(Exprs)));
                // ArithExpr TG = z3.MkAdd(Exprs);

                // BoolExpr Expr= z3.MkAnd(z3.MkGe(TG, TBPD), z3.MkLe(TG,z3.MkMul(TBPD, z3.MkReal(Convert.ToString((100.0 + THRESHOLD_DIFF) / 100.0)))));

                //new attack summation of load

                BoolExpr Expr = z3.MkAnd(z3.MkGe(TBPG, TBPD), z3.MkLe(TBPG, z3.MkMul(TBPD, z3.MkReal(Convert.ToString((100.0 + THRESHOLD_DIFF) / 100.0)))));
                opt.Assert(Expr);
            }
            #endregion

            #region MAX and MIN LIMIT of GENERATION
            {
                BoolExpr[] Exprs = new BoolExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    if (mBG[j])
                        Exprs[j - 1] = z3.MkEq(BPG[j], z3.MkAdd(z3.MkReal(Convert.ToString(minBPG[j])),
                            z3.MkMul(z3.MkReal(Convert.ToString(stepChangeBPG[j])), BoundPre[j])));
                    else
                        Exprs[j - 1] = z3.MkEq(BPG[j], Zero);
                }

                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
            }
            #endregion              

            #region BUS CONSUMPTION (GENRATION - LOAD)   
            {
                BoolExpr[] Exprs = new BoolExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    //Exprs[j - 1] = z3.MkEq(BP[j], z3.MkSub(BPD[j], BPG[j])); 
                    //Exprs[j - 1] = z3.MkEq(BP[j], z3.MkSub(Attack_Load[j], BPG[j]));
                    Exprs[j - 1] = z3.MkEq(BP[j], z3.MkSub(BPG[j], BPD[j])); 
                }
                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
            }
            #endregion

            #region BUS CONSUMPTION (SUM of POWER FLOW)
            {
                BoolExpr[] Exprs2 = new BoolExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    // If a bus is connected with NO bus, then the theta will be zero and 
                    // the power consumption at this bus will depend on its load only
                    if (connected[j, 0] == 0)
                    {
                        Exprs2[j - 1] = z3.MkEq(Theta[j], Zero);
                    }
                    else
                    {
                        ArithExpr[] Exprs = new ArithExpr[connected[j, 0]];
                        for (int i = 1; i <= connected[j, 0]; i++)
                        {
                            int k = mConnect[j, connected[j, i]];

                            if (j == powerLine[k, 0])
                                Exprs[i - 1] = FLP[k];
                            else
                                Exprs[i - 1] = BLP[k];
                        }
                        Exprs2[j - 1] = z3.MkEq(BP[j], z3.MkAdd(Exprs));
                    }
                }
                BoolExpr Expr = z3.MkAnd(Exprs2);
                opt.Assert(Expr);
            }
            #endregion

            #region COST of GENERATION
            {
                //BoolExpr[] Exprs = new BoolExpr[nBuses];
                ArithExpr[] Exprs = new ArithExpr[nGBuses];
                ArithExpr TCostPG;
                int k = 0;
                for (int j = 1; j <= nBuses; j++)
                {
                    if (mBG[j])
                        Exprs[k++] = z3.MkAdd(z3.MkReal(Convert.ToString(costCoef[j, 0])),
                            z3.MkMul(z3.MkReal(Convert.ToString(costCoef[j, 1])), BPG[j]));
                }

                TCostPG = z3.MkAdd(Exprs);
                // opt.Assert(z3.MkLe(TCostPG, ThCostPG));
                // opt.Assert(z3.MkEq(Cost, TCostPG));

                // Number of step changes to be considered for the power generation

                BoolExpr[] Exprs2 = new BoolExpr[nBuses];
                for (int j = 1; j <= nBuses; j++)
                {
                    if (mBG[j])
                        Exprs2[j - 1] = z3.MkAnd(z3.MkGe(BoundPre[j], z3.MkInt(0)), z3.MkLe(BoundPre[j], z3.MkInt(STEPS)));
                    else
                        Exprs2[j - 1] = z3.MkEq(BoundPre[j], z3.MkInt(0));
                    //Exprs[2 * j - 1] = z3.MkImplies(z3.MkNot(BG[j]), z3.MkEq(BoundPre[j], z3.MkInt(0)));
                }

                BoolExpr Expr = z3.MkAnd(Exprs2);
                opt.Assert(Expr);

                opt.Assert(z3.MkLe(TCostPG, ThCostPG));
                //opt.MkMaximize(TCostPG);
                opt.MkMinimize(TCostPG); // optimization formula
                opt.Assert(z3.MkEq(Cost, TCostPG));
            }
            #endregion

            #region GENERATION CONSTRAINTS (COMMENTED, we dont need this)
            // Number of step changes to be considered for the power generation (Commented, we don't need this)
            {
                ////BoolExpr[] Exprs = new BoolExpr[2 * nBuses];
                //BoolExpr[] Exprs = new BoolExpr[nBuses];
                //for (int j = 1; j <= nBuses; j++)
                //{
                //    if (mBG[j])
                //        Exprs[j - 1] = z3.MkAnd(z3.MkGe(BoundPre[j], z3.MkInt(0)), z3.MkLe(BoundPre[j], z3.MkInt(STEPS)));
                //    else
                //        Exprs[j - 1] = z3.MkEq(BoundPre[j], z3.MkInt(0));
                //    //Exprs[2 * j - 1] = z3.MkImplies(z3.MkNot(BG[j]), z3.MkEq(BoundPre[j], z3.MkInt(0)));
                //}

                //BoolExpr Expr = z3.MkAnd(Exprs);
                //opt.Assert(Expr);

                // opt.Assert(z3.MkLe(TCostPG, ThCostPG));
                // opt.Assert(z3.MkEq(Cost, TCostPG));
            }
            #endregion            

            #region The difference between Thetas of two connecting buses (COMMENTED, we dont need this)
            // The summation of the line power flows
            {
                //BoolExpr[] Exprs = new BoolExpr[2 * nLines];

                //for (int i = 1; i <= nLines; i++)
                //{
                //    int j1 = powerLine[i, 0];
                //    int j2 = powerLine[i, 1];

                //    Exprs[2 * i - 2] = z3.MkImplies(z3.MkGt(Theta[j1], Theta[j2]),
                //        z3.MkLe(z3.MkSub(Theta[j1], Theta[j2]), z3.MkReal(Convert.ToString(THRESHOLD_THETA_DIFF))));

                //    Exprs[2 * i - 1] = z3.MkImplies(z3.MkLt(Theta[j1], Theta[j2]),
                //        z3.MkLe(z3.MkSub(Theta[j2], Theta[j1]), z3.MkReal(Convert.ToString(THRESHOLD_THETA_DIFF))));

                //    //Exprs[2 * i - 1] = z3.MkImplies(z3.MkLt(Theta[j1], Theta[j2]), 
                //    //    z3.MkGe(z3.MkSub(Theta[j1], Theta[j2]), z3.MkReal(Convert.ToString(-THRESHOLD_THETA_DIFF))));
                //}

                //BoolExpr Expr = z3.MkAnd(Exprs);
                //opt.Assert(Expr);

            }
            #endregion

            #region FLP and BLP (using theta * admittance)
            {
                BoolExpr[] Exprs = new BoolExpr[nLines];
                for (int i = 1; i <= nLines; i++)
                {
                    // Based on real topology
                    Exprs[i - 1] = z3.MkEq(FLP[i],
                        z3.MkMul(z3.MkSub(Theta[powerLine[i, 0]], Theta[powerLine[i, 1]]),
                            z3.MkReal(Convert.ToString(lineAdmittance[i]))));
                }
                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
            }
            {
                BoolExpr[] Exprs = new BoolExpr[nLines];
                for (int i = 1; i <= nLines; i++)
                {
                    Exprs[i - 1] = z3.MkEq(BLP[i],
                                     z3.MkMul(z3.MkSub(Theta[powerLine[i, 1]], Theta[powerLine[i, 0]]),
                                         z3.MkReal(Convert.ToString(lineAdmittance[i]))));
                }
                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
            }

            // The phase angle of the reference bus is zero
            {
                BoolExpr Expr = z3.MkEq(Theta[refBus], z3.MkReal(0));
                opt.Assert(Expr);
            }
            #endregion

            #region FLP and BLP CAPACITY LIMIT (LINE FLOW) 
            {
                BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                
                for (int i = 1; i <= nLines; i++)
                {
                    double minPL = (-1) * maxPL[i];
                    Exprs[2 * i - 2] = z3.MkAnd(z3.MkGe(FLP[i], z3.MkReal(Convert.ToString(minPL))),
                        z3.MkLe(FLP[i], z3.MkReal(Convert.ToString(maxPL[i]))));
                    // It will automatically cover the constraint for backward power flow
                    Exprs[2 * i - 1] = z3.MkAnd(z3.MkGe(BLP[i], z3.MkReal(Convert.ToString(minPL))),
                        z3.MkLe(BLP[i], z3.MkReal(Convert.ToString(maxPL[i]))));
                }
                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
            }
            #endregion

            #region (n-1) LINE CONTINGENCY FLOW (both forward and backward)
            {
                for (int k = 1; k <= nLines; k++)
                {
                    for (int l = 1; l <= nLines; l++)
                    {
                        if (l != k)
                        {
                            RealExpr Delta_FLP = (RealExpr)z3.MkMul(FLP[k], z3.MkReal(Convert.ToString(LODF[l - 1, k - 1])));
                            RealExpr Changed_FLP = (RealExpr)z3.MkAdd(FLP[l], Delta_FLP);
                            opt.Assert(z3.MkEq(Lines_Contingency_Flow[k, l], Changed_FLP));
                        }
                        else
                        {
                            opt.Assert(z3.MkEq(Lines_Contingency_Flow[k, l], Zero));
                        }
                    }
                }
                for (int k = 1; k <= nLines; k++)
                {
                    for (int l = 1; l <= nLines; l++)
                    {
                        BoolExpr Expr = z3.MkEq(Back_Lines_Contingency_Flow[k, l], z3.MkSub(Zero, Lines_Contingency_Flow[k, l]));
                        opt.Assert(Expr);                        
                    }
                }
            }
            #endregion

            #region CONTINGENCY FLOW MAX LIMIT (forward and backward)
            // If after contingency each line is in LIMIT or NOT??
            {
                //BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                BoolExpr[] Exprs = new BoolExpr[nLines];
                for (int i = 1; i <= nLines; i++)
                {
                    BoolExpr[] OneLineOut = new BoolExpr[2 * nLines];
                    for (int j = 1; j <= nLines; j++)
                    {
                        double minPL = (-1) * maxPL[j];

                        OneLineOut[2 * j - 2] = z3.MkAnd(z3.MkGe(Lines_Contingency_Flow[i,j], z3.MkReal(Convert.ToString(minPL))),
                       z3.MkLe(Lines_Contingency_Flow[i, j], z3.MkReal(Convert.ToString(maxPL[j]))));
                        // It will automatically cover the constraint for backward power flow
                        OneLineOut[2 * j - 1] = z3.MkAnd(z3.MkGe(Back_Lines_Contingency_Flow[i,j], z3.MkReal(Convert.ToString(minPL))),
                            z3.MkLe(Back_Lines_Contingency_Flow[i,j], z3.MkReal(Convert.ToString(maxPL[j]))));
                    }
                    Exprs[i - 1] = z3.MkAnd(OneLineOut);                   
                }
                BoolExpr Expr = z3.MkAnd(Exprs);
                opt.Assert(Expr);
            }
            #endregion

            #endregion            
        }
        #endregion

        #region  enumerate
        void Enumerate(Context z3, Optimize opt)
        {
            int numOfSol = 0;
            bool isSat = false;
            Model model = null;
            //Status st = slv.Check();
            Status ot = opt.Check();

            while (opt.Check() == Status.SATISFIABLE)           
            {
                isSat = true;
               // model = slv.Model;
                model = opt.Model;

                numOfSol++;
               
                Console.WriteLine("REAL LOAD");
                
                for (int i = 1; i <= nBuses; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    Console.WriteLine("Bus {0} ", i + " real load: " + Math.Round(ToDouble(model.Eval(BPD[i]).ToString()), 5));
                     tw.WriteLine("Bus {0} ", i + " real load: " + Math.Round(ToDouble(model.Eval(BPD[i]).ToString()), 5));
                }
                
                Console.WriteLine();
                /*
                Console.WriteLine("DELTA LOAD");
                for (int i = 1; i <= nBuses; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                   // Console.WriteLine("Bus load {0} ", i + " changed: " + model.Eval(Delta_Load[i]).ToString());
                    Console.WriteLine("Bus load {0} ", i + " changed: " + Math.Round(ToDouble(model.Eval(Delta_Load[i]).ToString()), 5));
                    tw.WriteLine("Bus load {0} ", i + " changed: " + Math.Round(ToDouble(model.Eval(Delta_Load[i]).ToString()), 5));
                }

                Console.WriteLine();
                */
                Console.WriteLine("CHANGED LOAD");                
                for (int i = 1; i <= nBuses; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    //Console.WriteLine("Bus {0} ", i + " changed load: " + Math.Round(ToDouble(model.Eval(Attack_Load[i]).ToString()), 5));
                    // tw.WriteLine("Bus {0} ", i + " changed load: " + Math.Round(ToDouble(model.Eval(Attack_Load[i]).ToString()), 5));
                }                
                Console.WriteLine();

                Console.WriteLine("GENERATION");
                for (int i = 1; i <= nBuses; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    Console.WriteLine("Bus {0} ", i + " generation: " + Math.Round(ToDouble(model.Eval(BPG[i]).ToString()), 5));
                    tw.WriteLine("Bus {0} ", i + " generation: " + Math.Round(ToDouble(model.Eval(BPG[i]).ToString()), 5));
                }

                Console.WriteLine();                

                Console.WriteLine("LINE FLOW AFTER CONTINGENCY");                
                for (int i = 1; i <= nLines; i++)
                {
                    Console.WriteLine("Line {0} out: ", i);
                    tw.WriteLine("Line {0} out: ", i);
                    for (int j = 1; j <= nLines; j++)
                    {                     
                        Console.WriteLine("flow in line {0}", j + ": " + Math.Round(ToDouble(model.Eval(Lines_Contingency_Flow[i, j]).ToString()),5));
                        tw.WriteLine("flow in line {0}", j + ": " + Math.Round(ToDouble(model.Eval(Lines_Contingency_Flow[i, j]).ToString()), 5));
                    }
                    Console.WriteLine();
                }                
                Console.WriteLine();
                
                Console.WriteLine("TOTAL REAL LOAD: " + Math.Round(ToDouble(model.Eval(TBPD).ToString()), 5));
                tw.WriteLine("TOTAL REAL LOAD" + Math.Round(ToDouble(model.Eval(TBPD).ToString()), 5));
                Console.WriteLine();
/*
                Console.WriteLine("TOTAL CHANGED LOAD: " + Math.Round(ToDouble(model.Eval(TotalAttackLoad).ToString()), 5));
                tw.WriteLine("TOTAL CHANGED LOAD" + Math.Round(ToDouble(model.Eval(TotalAttackLoad).ToString()), 5));
                Console.WriteLine();
                */
                Console.WriteLine("TOTAL GENERATION: " + Math.Round(ToDouble(model.Eval(TBPG).ToString()), 5));
                tw.WriteLine("TOTAL GENERATION" + Math.Round(ToDouble(model.Eval(TBPG).ToString()), 5));

                Console.WriteLine();

                /*
                Console.WriteLine("FLP (using Theta * Admittance)");                
                for (int i = 1; i <= nLines; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    Console.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(FLP[i]).ToString()), 5));
                    tw.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(FLP[i]).ToString()), 5));
                }
                
                Console.WriteLine();

                Console.WriteLine("Original FLOW (using SHIFT FACTOR)");
                
                for (int i = 1; i <= nLines; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    //Console.WriteLine("flow in line {0} ", i + ": " + model.Eval(SF_Flow[i]));
                    Console.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(SF_Flow[i]).ToString()), 5));
                    tw.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(SF_Flow[i]).ToString()), 5));
                }
                
                Console.WriteLine();
                */
                /*
                Console.WriteLine("Backward FLOW using SHIFT FACTOR");
                
                for (int i = 1; i <= nLines; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    //Console.WriteLine("flow in line {0} ", i + ": " + model.Eval(SF_Flow[i]));
                    Console.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(Back_SF_Flow[i]).ToString()), 5));
                    tw.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(Back_SF_Flow[i]).ToString()), 5));
                }

                Console.WriteLine();
                */
                /*
                Console.WriteLine("Overflow STATUS");
                for (int i = 1; i <= nLines; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    //Console.WriteLine("flow in line {0} ", i + ": " + model.Eval(SF_Flow[i]));
                    Console.WriteLine("line {0} ", i + " overflow: " + model.Eval(IsOverFlow[i]).ToString());
                    tw.WriteLine("line {0} ", i + " overflow: " + model.Eval(IsOverFlow[i]).ToString());
                }

                Console.WriteLine();

                Console.WriteLine("Overflow STATUS (Debug)");
                for (int i = 1; i <= nLines; i++)
                {
                    //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                    //Console.WriteLine("flow in line {0} ", i + ": " + model.Eval(SF_Flow[i]));
                    Console.WriteLine("line {0} ", i + " overflow: " + model.Eval(OverLineCount[i]).ToString());
                    tw.WriteLine("line {0} ", i + " overflow: " + model.Eval(OverLineCount[i]).ToString());
                }

                Console.WriteLine();

                Console.WriteLine("Original FLOW after Contingency (using SHIFT FACTOR)");
                
                for (int i = 1; i <= nLines; i++)
                {
                    Console.WriteLine("Line {0} out: ", i);
                    tw.WriteLine("Line {0} out: ", i);
                    for (int j = 1; j <= nLines; j++)
                    {
                        Console.WriteLine("flow in line {0}", j + ": " + Math.Round(ToDouble(model.Eval(SF_Lines_Contingency_Flow[i, j]).ToString()), 5));
                        tw.WriteLine("flow in line {0}", j + ": " + Math.Round(ToDouble(model.Eval(SF_Lines_Contingency_Flow[i, j]).ToString()), 5));

                        Console.WriteLine("line {0} ", j + " overflow: " + model.Eval(IsOverFlowContgn[i, j]).ToString());

                    }
                    Console.WriteLine();
                }
                
                Console.WriteLine();
                */
                /*
                Console.WriteLine("Contingency Overflow STATUS");
                for (int i = 1; i <= nLines; i++)
                {
                    Console.WriteLine("Line {0} out: ", i);
                    tw.WriteLine("Line {0} out: ", i);
                    for (int j = 1; j <= nLines; j++)
                    {
                        //tw2.Write("{0} ", model.Eval(FLP[i]).ToString());
                        //Console.WriteLine("flow in line {0} ", i + ": " + model.Eval(SF_Flow[i]));
                        Console.WriteLine("line {0} ", i + " overflow: " + model.Eval(IsOverFlowContgn[i]).ToString());
                        tw.WriteLine("line {0} ", i + " overflow: " + model.Eval(IsOverFlowContgn[i]).ToString());
                    }
                }
                */
                //SCOPF COST Calculation

                Console.WriteLine("SCOPF Cost found: " + Math.Round(ToDouble(model.Eval(Cost).ToString())));
                tw.WriteLine("SCOPF Cost found: " + Math.Round(ToDouble(model.Eval(Cost).ToString())));
                //test case
                //Console.WriteLine("A values " + model.Eval(a).ToString());
                //tw.WriteLine("A values " + model.Eval(a).ToString());
                //Console.WriteLine("B values " + model.Eval(b).ToString());
                //tw.WriteLine("B values " + model.Eval(b).ToString());

                tw.WriteLine("===============================================================");

                if (numOfSol == 1)
                {
                    Console.WriteLine("total solution: {0}" , numOfSol);
                    break;
                }
            }


            if(!isSat)
           // if (ot == Status.UNSATISFIABLE || ot == Status.UNKNOWN)
            //if (st == Status.UNSATISFIABLE || st == Status.UNKNOWN)
            {
                
                Console.WriteLine("We have no solution");
                tw.WriteLine("We have no solution");
            }
            
        }
        #endregion

        #region model
        void Model()
        {
            Global.SetParameter("SMT.ARITH.RANDOM_INITIAL_VALUE", "true");
            Global.SetParameter("SMT.RANDOM_SEED", "6");
            try
            {
                Console.Write("Z3 Major Version: ");
                Console.WriteLine(Microsoft.Z3.Version.Major.ToString());
                Console.Write("Z3 Full Version: ");
                Console.WriteLine(Microsoft.Z3.Version.ToString() + "\n");

                Dictionary<string, string> cfg = new Dictionary<string, string>() {
                { "MODEL", "true"}
                //{ "TIMEOUT", "10"}
                };

                z3 = new Context(cfg);
               // slv = z3.MkSolver();
                opt = z3.MkOptimize();
                ReadInput(z3,opt);          
                
                Formalize(z3,opt);
                Enumerate(z3,opt);

                Console.WriteLine("Functions Done");
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
            Console.WriteLine("SCOPF Program");
            Stopwatch stopWatch = new Stopwatch();
            stopWatch.Start();

            tw = new StreamWriter("Output.txt", true);
            tw.WriteLine("===============================================================");
            tw.WriteLine("SCOPF Program");
            CaOpf oIn = new CaOpf();
            oIn.Model();
            //pIn.z3 = new Context(cfg);
            //slv = z3.MkSolver();
            Console.WriteLine("Program ends");
            stopWatch.Stop();
            Console.WriteLine("Total Required time: {0}", stopWatch.Elapsed.TotalSeconds);
            tw.WriteLine("Total Required time: {0}", stopWatch.Elapsed.TotalSeconds);
            tw.WriteLine("Program Ends");
            tw.WriteLine("===============================================================");

            tw.Close();
           
        }
    }
}
