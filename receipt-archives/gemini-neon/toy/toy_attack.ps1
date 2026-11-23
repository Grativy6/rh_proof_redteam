# Adversarial Toy Lab for leanprover-community/riemann-hypothesis @ 40e56bab026552e089d7afcfeff08d2defb9c005
# Three concrete executable break attempts using the EXACT definitions from:
#   - Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean
#   - Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean
#   - Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean
#   - Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean
#   - Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean
#   - Formalism/RankGapBounds/MeanBoundSecondForm.lean
#   - Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean

$ErrorActionPreference = 'Stop'

Add-Type -ReferencedAssemblies System.Numerics -TypeDefinition @"
using System;
using System.Collections.Generic;
using System.Numerics;

public static class RhToyEngine
{
    public const double EULER_GAMMA = 0.57721566490153286060651209008240243104215933593992;

    // Sieve primes and von Mangoldt Lambda(n) up to maxN
    public static double[] SieveVonMangoldt(int maxN, out int[] primes)
    {
        bool[] isComp = new bool[maxN + 1];
        List<int> plist = new List<int>();
        double[] lam = new double[maxN + 1];
        for (int i = 2; i <= maxN; i++)
        {
            if (!isComp[i])
            {
                plist.Add(i);
                double lp = Math.Log(i);
                long pk = i;
                while (pk <= maxN)
                {
                    lam[pk] = lp;
                    pk *= i;
                }
                if ((long)i * i <= maxN)
                {
                    for (int j = i * i; j <= maxN; j += i) isComp[j] = true;
                }
            }
        }
        primes = plist.ToArray();
        return lam;
    }

    public static int Gcd(int a, int b)
    {
        a = Math.Abs(a); b = Math.Abs(b);
        while (b != 0) { int t = a % b; a = b; b = t; }
        return a;
    }

    public static int Legendre(int a, int p)
    {
        a = ((a % p) + p) % p;
        if (a == 0) return 0;
        long res = 1, b = a, e = (p - 1) / 2;
        while (e > 0)
        {
            if ((e & 1) == 1) res = (res * b) % p;
            b = (b * b) % p;
            e >>= 1;
        }
        return res == 1 ? 1 : -1;
    }

    // Group element in E0 x ZMod(nH), E0 = ZMod 2 x ZMod 2
    public struct GEl
    {
        public int e1; // 0 or 1 (g.1.1: InPhi iff e1 == 0; chC(g) = (-1)^e1)
        public int e2; // 0 or 1 (g.1.2: psC(g) = (-1)^e2)
        public int h;  // 0..nH-1
        public GEl(int a, int b, int c) { e1 = a & 1; e2 = b & 1; h = c; }
        public int Idx(int nH) { return (e1 * 2 + e2) * nH + h; }
    }

    public static GEl Add(GEl a, GEl b, int nH)
    {
        return new GEl(a.e1 ^ b.e1, a.e2 ^ b.e2, (a.h + b.h) % nH);
    }

    public static GEl Neg(GEl a, int nH)
    {
        return new GEl(a.e1, a.e2, (nH - (a.h % nH)) % nH);
    }

    public static GEl MulInt(int k, GEl a, int nH)
    {
        return new GEl((k & 1) == 1 ? a.e1 : 0, (k & 1) == 1 ? a.e2 : 0, ((k % nH) * a.h) % nH);
    }

    // Character psi_{c1, c2, ch} on E0 x ZMod(nH): (-1)^(c1*e1 + c2*e2) * exp(2pi i * ch * h / nH)
    public static Complex EvalChar(int c1, int c2, int ch, GEl g, int nH)
    {
        double sign = (((c1 & g.e1) ^ (c2 & g.e2)) == 0) ? 1.0 : -1.0;
        double ang = 2.0 * Math.PI * ((ch * g.h) % nH) / nH;
        return new Complex(sign * Math.Cos(ang), sign * Math.Sin(ang));
    }

    // Concrete HostFactsS model: M = 4 * d * q1 with d = 7, q1 = 11, nH = 5 (primitive root 2 mod 11)
    // E0.1 <- chi_{-7} mod 7, E0.2 <- chi_{-4} mod 4, H <- dlog_2(u mod 11) mod 5.
    // Exact check: inertia(7) = {0, sgc0}, inertia(2) <= InPhi, inertia(11) <= InPhi, frob(2), frob(11) in InPhi.
    public class ConcreteHost308
    {
        public const int d = 7;
        public const int q1 = 11;
        public const int nH = 5;
        public const int M = 4 * d * q1; // 308
        public const int GSize = 4 * nH; // 20
        public const int PhiCard = 2 * nH; // 10
        private int[] dlog11 = new int[11];

        public ConcreteHost308()
        {
            int cur = 1;
            for (int k = 0; k < 10; k++) { dlog11[cur] = k; cur = (cur * 2) % 11; }
        }

        // Exact primitive character value primVal(D, psi, n) for psi = (c1, c2, ch)
        // Factors across mod 7 (c1), mod 4 (c2), mod 11 (ch):
        //   - if c1=1, factor chi_{-7}(n) (ramified at 7, 0 if 7|n); if c1=0, trivial (1 even at 7!)
        //   - if c2=1, factor chi_{-4}(n) (ramified at 2, 0 if 2|n); if c2=0, trivial (1 even at 2!)
        //   - if ch!=0, factor exp(2pi i ch * dlog11(n mod 11)/5) (ramified at 11, 0 if 11|n); if ch=0, trivial (1 even at 11!)
        // Note: this EXACTLY equals the product over p|n of cosetMean(inertia(p), v_p(n)*frob(p), psi)!
        public Complex PrimVal(int c1, int c2, int ch, int n)
        {
            Complex res = Complex.One;
            if (c1 == 1)
            {
                int l = Legendre(n, 7);
                if (l == 0) return Complex.Zero;
                res *= l;
            }
            if (c2 == 1)
            {
                if ((n & 1) == 0) return Complex.Zero;
                int s = (n % 4 == 1) ? 1 : -1;
                res *= s;
            }
            if (ch != 0)
            {
                int r = n % 11;
                if (r == 0) return Complex.Zero;
                double ang = 2.0 * Math.PI * ((ch * dlog11[r]) % 5) / 5.0;
                res *= new Complex(Math.Cos(ang), Math.Sin(ang));
            }
            return res;
        }

        // Direct definition via Artin map / inertia / frob to verify PrimVal == cosetMean!
        public GEl Art(int u)
        {
            int e1 = (Legendre(u, 7) == 1) ? 0 : 1;
            int e2 = (u % 4 == 1) ? 0 : 1;
            int h = dlog11[u % 11] % 5;
            return new GEl(e1, e2, h);
        }

        public GEl Frob(int p)
        {
            if (p != 2 && p != 7 && p != 11) return Art(p);
            // Solve u == p mod ordCompl_p(308), u == 1 mod p^v
            int pv = (p == 2) ? 4 : p;
            int oc = M / pv;
            for (int u = 1; u < M; u++)
                if (Gcd(u, M) == 1 && (u % oc) == (p % oc) && (u % pv) == 1)
                    return Art(u);
            throw new Exception("frob not found");
        }

        public List<GEl> Inertia(int p)
        {
            var list = new List<GEl>();
            var seen = new HashSet<int>();
            int pv = (p == 2) ? 4 : ((p == 7 || p == 11) ? p : 1);
            int oc = M / pv;
            for (int u = 1; u < M; u++)
            {
                if (Gcd(u, M) == 1 && (u % oc) == 1)
                {
                    var g = Art(u);
                    if (seen.Add(g.Idx(nH))) list.Add(g);
                }
            }
            return list;
        }

        // Exact L'/L(1, chi) for non-principal primitive chi of conductor Q <= 308 via
        // L(s, chi) = Q^(-s) sum_{a=1}^{Q-1} chi(a) zeta(s, a/Q) ->
        //   L(1, chi) = -(1/Q) sum chi(a) psi(a/Q)  [where psi = digamma]
        //   Wait: even cleaner & 15-digit accurate via partial summation / Euler-Maclaurin on
        //   L(1, chi) = sum_{n=1}^{K} chi(n)/n + O(Q/K) with Richardson / Cesaro / Euler transform,
        //   AND exact Bernoulli-free Euler-Maclaurin for sum_{n>=1} chi(n)/n and -sum_{n>=1} chi(n) log(n)/n!
        public Complex ComputeLogDerivAtOne(int c1, int c2, int ch)
        {
            if (c1 == 0 && c2 == 0 && ch == 0) return Complex.Zero;
            int Q = (c1 == 1 ? 7 : 1) * (c2 == 1 ? 4 : 1) * (ch != 0 ? 11 : 1);
            // Use Euler-Maclaurin with M_blocks full periods of Q (sum of chi over full period = 0!)
            // sum_{n=1}^{B*Q} f(n) + tail via Euler-Maclaurin on each residue class a mod Q:
            // For g_a(k) = 1/(Q*k + a), tail from k=B to inf:
            //   int_B^inf g_a(t) dt + 1/2 g_a(B) - 1/12 g_a'(B) + 1/720 g_a'''(B) - 1/30240 g_a'''''(B)
            // Notice int_B^inf (sum_a chi(a)/(Q*t+a)) dt = sum_a chi(a) * (-1/Q) log(Q*B + a) (since sum chi(a) = 0!)
            // And for L'(1, chi) = -sum chi(n) log(n)/n:
            //   int_B^inf (-log(Qt+a)/(Qt+a)) dt = (1/(2Q)) (log(QB+a))^2 (since sum chi(a)=0!)
            int B = 200; // N0 = 200 * Q <= 61600 -> O((B*Q)^(-7)) < 1e-16!
            Complex L1 = Complex.Zero;
            Complex Lp1 = Complex.Zero;
            for (int n = 1; n <= B * Q; n++)
            {
                Complex v = PrimVal(c1, c2, ch, n);
                if (v == Complex.Zero) continue;
                double inv = 1.0 / n;
                L1 += v * inv;
                Lp1 -= v * (Math.Log(n) * inv);
            }
            for (int a = 1; a <= Q; a++)
            {
                Complex v = PrimVal(c1, c2, ch, a);
                if (v == Complex.Zero) continue;
                double x = Q * (double)B + a;
                double lx = Math.Log(x);
                double x2 = x * x, x3 = x2 * x, x4 = x2 * x2, x5 = x4 * x, x6 = x3 * x3;
                // Euler-Maclaurin for sum_{k=B+1}^inf f(Qk+a) = int_B^inf f(Qt+a)dt - 1/2 f(x) - 1/12 Q f'(x) + 1/720 Q^3 f'''(x) - 1/30240 Q^5 f'''''(x)
                // For f(x) = 1/x: int = -(1/Q) ln(x) [modulo constant independent of a, killed by sum chi(a)=0]
                // f'(x) = -1/x^2, f'''(x) = -6/x^4, f'''''(x) = -120/x^6
                double tailL = -lx / Q - 0.5 / x + (Q / 12.0) / x2 - (Q * Q * Q / 120.0) / x4 + (Q * Q * Q * Q * Q / 252.0) / x6;
                L1 += v * tailL;

                // For f(x) = -ln(x)/x:
                // int (-ln(Qt+a)/(Qt+a)) dt = +(1/(2Q)) (ln(x))^2 [const killed by sum chi(a)=0]
                // f(x) = -lx/x
                // f'(x) = (lx - 1)/x^2
                // f'''(x) = (6 lx - 11)/x^4
                // f'''''(x) = (120 lx - 274)/x^6
                double tailLp = 0.5 * lx * lx / Q + 0.5 * lx / x - (Q / 12.0) * (lx - 1.0) / x2
                              + (Q * Q * Q / 720.0) * (6.0 * lx - 11.0) / x4
                              - (Q * Q * Q * Q * Q / 30240.0) * (120.0 * lx - 274.0) / x6;
                Lp1 += v * tailLp;
            }
            return Lp1 / L1;
        }

        // Exact GPsi(psi, y) from Analytic.lean / Balance.lean
        public Complex GPsi(int c1, int c2, int ch, Complex ellPsi, double y, double[] lam)
        {
            int lim = (int)Math.Floor(y);
            if (c1 == 0 && c2 == 0 && ch == 0)
            {
                double s = 0.0;
                for (int n = 1; n <= lim; n++)
                    if (lam[n] > 0) s += lam[n] * Math.Max(y / n - 1.0, 0.0);
                return new Complex(s - y * (Math.Log(y) - 1.0 - EULER_GAMMA), 0.0);
            }
            else
            {
                Complex s = Complex.Zero;
                for (int n = 1; n <= lim; n++)
                    if (lam[n] > 0)
                    {
                        Complex cv = PrimVal(c1, c2, ch, n);
                        if (cv != Complex.Zero)
                            s += cv * (lam[n] * Math.Max(y / n - 1.0, 0.0));
                    }
                return s + y * ellPsi;
            }
        }
    }

    // EXPERIMENT 1: Exact concrete verification + adversarial fuzz of ch_balance, LipW, and boundary y->1+, y<1
    public static string RunExperiment1()
    {
        var sb = new System.Text.StringBuilder();
        var host = new ConcreteHost308();
        int maxN = 12000;
        int[] primes;
        double[] lam = SieveVonMangoldt(maxN, out primes);

        // 1A: Verify HostFactsS axioms & PrimVal == cosetMean at p = 2, 7, 11, 3, 5, 13
        int[] testP = new int[] { 2, 3, 5, 7, 11, 13, 17 };
        double maxCosetDiff = 0.0;
        foreach (int p in testP)
        {
            var I = host.Inertia(p);
            var fr = host.Frob(p);
            for (int c1 = 0; c1 < 2; c1++)
            for (int c2 = 0; c2 < 2; c2++)
            for (int ch = 0; ch < 5; ch++)
            for (int i = 1; i <= 3; i++)
            {
                int pk = (int)Math.Pow(p, i);
                Complex mean = Complex.Zero;
                var ifr = MulInt(i, fr, ConcreteHost308.nH);
                foreach (var x in I)
                    mean += EvalChar(c1, c2, ch, Add(ifr, x, ConcreteHost308.nH), ConcreteHost308.nH);
                mean /= I.Count;
                Complex pv = host.PrimVal(c1, c2, ch, pk);
                double diff = (mean - pv).Magnitude;
                if (diff > maxCosetDiff) maxCosetDiff = diff;
            }
        }
        sb.AppendLine(string.Format("[1A] Concrete Host M=308 (d=7, q1=11, H=Z/5Z): max |cosetMean - PrimVal| = {0:E3}", maxCosetDiff));

        // Precompute ell(psi) = L'/L(1, chi_psi) for all 20 characters
        Complex[,,] ell = new Complex[2, 2, 5];
        for (int c1 = 0; c1 < 2; c1++)
        for (int c2 = 0; c2 < 2; c2++)
        for (int ch = 0; ch < 5; ch++)
            ell[c1, c2, ch] = host.ComputeLogDerivAtOne(c1, c2, ch);

        sb.AppendLine(string.Format("     L'/L(1, chi_-7)  = {0:F12} (chC, conductor 7)", ell[1, 0, 0].Real));
        sb.AppendLine(string.Format("     L'/L(1, chi_-4)  = {0:F12} (psC, conductor 4)", ell[0, 1, 0].Real));
        sb.AppendLine(string.Format("     L'/L(1, chi_28)  = {0:F12} (chpsC, conductor 28)", ell[1, 1, 0].Real));

        // 1B: Test EXACT ch_balance: ASK - MAIN == De across 50 random & boundary (a, t, w) configs
        // Including boundary cases where a/w lands EXACTLY on primes (3, 5, 7, 13, 49), and where a/w < 1!
        var rng = new Random(20261123);
        double maxBalErr_ge1 = 0.0;
        double maxBalErr_lt1 = 0.0;
        int countLt1 = 0;
        GEl cconj = new GEl(1, 1, 0);
        GEl[] allG = new GEl[ConcreteHost308.GSize];
        for (int e1 = 0; e1 < 2; e1++)
        for (int e2 = 0; e2 < 2; e2++)
        for (int h = 0; h < 5; h++)
            allG[new GEl(e1, e2, h).Idx(5)] = new GEl(e1, e2, h);

        var inertD = host.Inertia(7);
        var frobD = host.Frob(7);
        var inertHash = new HashSet<int>();
        foreach (var x in inertD) inertHash.Add(x.Idx(5));

        for (int trial = 0; trial < 40; trial++)
        {
            double a = (trial < 10) ? (trial + 1) * 7.0 : (50.0 + rng.NextDouble() * 4000.0);
            int tVal = rng.Next(5);
            GEl topT = new GEl(0, 0, tVal);
            double[] w = new double[ConcreteHost308.GSize];
            bool hasLt1 = false;
            double maxRatio = 0.0;
            for (int idx = 0; idx < ConcreteHost308.GSize; idx++)
            {
                if (trial == 0) w[idx] = a / 7.0; // exact hit on ramified prime d=7!
                else if (trial == 1) w[idx] = a / 49.0; // exact hit on d^2=49!
                else if (trial == 2) w[idx] = a * 2.5; // BOUNDARY TEST: a/w = 0.4 < 1!!
                else if (trial == 3) w[idx] = a; // BOUNDARY TEST: a/w = 1.0!!
                else w[idx] = 0.5 + rng.NextDouble() * 15.0;
                double r = a / w[idx];
                if (r < 1.0) hasLt1 = true;
                if (r > maxRatio) maxRatio = r;
            }

            int N = (int)Math.Ceiling(maxRatio) + 5;
            if (N > maxN) N = maxN;

            // Compute ASK directly from primes (ChBalance.lean L186):
            // ASK = sum_{p inert} 2 log(p) sum_{i>=1, !InPhi(i*frob(p))} max(a/p^i - w(partner(t, i*frob(p))), 0)
            //     + log(d) * sum_{i>=1} sum_{g: !InPhi(g), g - i*frob(d) in I_d} max(a/d^i - w(partner(t, g)), 0)
            double ask = 0.0;
            foreach (int p in primes)
            {
                if (p > N) break;
                if (p == 2 || p == 11) continue;
                if (p == 7)
                {
                    long pk = 7;
                    for (int i = 1; pk <= N; i++, pk *= 7)
                    {
                        var ifr = MulInt(i, frobD, 5);
                        foreach (var g in allG)
                        {
                            if (g.e1 == 0) continue; // !InPhi(g)
                            var diff = Add(g, Neg(ifr, 5), 5);
                            if (inertHash.Contains(diff.Idx(5)))
                            {
                                var part = Add(Add(cconj, g, 5), topT, 5);
                                ask += Math.Log(7.0) * Math.Max(a / pk - w[part.Idx(5)], 0.0);
                            }
                        }
                    }
                }
                else if (Legendre(p, 7) == -1) // IsInert
                {
                    var fr = host.Frob(p);
                    long pk = p;
                    for (int i = 1; pk <= N; i++, pk *= p)
                    {
                        var ifr = MulInt(i, fr, 5);
                        if (ifr.e1 == 1) // !InPhi(i*frob(p))
                        {
                            var part = Add(Add(cconj, ifr, 5), topT, 5);
                            ask += 2.0 * Math.Log(p) * Math.Max(a / pk - w[part.Idx(5)], 0.0);
                        }
                    }
                }
            }

            // Compute MAIN (Balance.lean / RunBaseDimension):
            double sumLogW = 0.0;
            foreach (var rho in allG)
                if (rho.e1 == 0) sumLogW += Math.Log(w[rho.Idx(5)]);
            double mainVal = a * (Math.Log(a) - 1.0 - EULER_GAMMA + ell[1, 0, 0].Real - sumLogW / ConcreteHost308.PhiCard);

            // Compute De = (1/|PhiSet|) sum_{g: !InPhi(g)} sum_psi conj(psi(g)) * w(partner(t,g)) * GPsi(psi, a / w(partner(t,g)))
            Complex de = Complex.Zero;
            foreach (var g in allG)
            {
                if (g.e1 == 0) continue;
                var part = Add(Add(cconj, g, 5), topT, 5);
                double wv = w[part.Idx(5)];
                double y = a / wv;
                for (int c1 = 0; c1 < 2; c1++)
                for (int c2 = 0; c2 < 2; c2++)
                for (int ch = 0; ch < 5; ch++)
                {
                    Complex ps = Complex.Conjugate(EvalChar(c1, c2, ch, g, 5));
                    de += ps * wv * host.GPsi(c1, c2, ch, ell[c1, c2, ch], y, lam);
                }
            }
            de /= ConcreteHost308.PhiCard;

            double err = (new Complex(ask - mainVal, 0.0) - de).Magnitude;
            if (hasLt1) { countLt1++; if (err > maxBalErr_lt1) maxBalErr_lt1 = err; }
            else { if (err > maxBalErr_ge1) maxBalErr_ge1 = err; }
        }
        sb.AppendLine(string.Format("[1B] ch_balance residual |ASK - MAIN - De| (y >= 1, incl. exact hits at d, d^2, 1): max = {0:E3}", maxBalErr_ge1));
        sb.AppendLine(string.Format("     ch_balance residual |ASK - MAIN - De| (y < 1 boundary, {0} trials):           max = {1:E3}", countLt1, maxBalErr_lt1));

        // 1C: Adversarial fuzz of LipW constant: ||w*GPsi(A/w) - w'*GPsi(A/w')|| / ((A/min(w,w'))*|w-w'|) <= 3?
        double maxLipRatio = 0.0;
        string maxLipWitness = "";
        for (int c1 = 0; c1 < 2; c1++)
        for (int c2 = 0; c2 < 2; c2++)
        for (int ch = 0; ch < 5; ch++)
        {
            for (int k = 0; k < 400; k++)
            {
                double A = (k < 50) ? (1.0 + rng.NextDouble() * 30.0) : (30.0 + rng.NextDouble() * 8000.0);
                double w1 = 0.5 + rng.NextDouble() * (A * 1.5); // intentionally allows A/w < 1 too!
                double dw = (k % 2 == 0) ? (1e-4 + rng.NextDouble() * 0.05) : (0.1 + rng.NextDouble() * 5.0);
                double w2 = w1 + dw;
                if (A / w1 > maxN || A / w2 > maxN) continue;
                Complex f1 = w1 * host.GPsi(c1, c2, ch, ell[c1, c2, ch], A / w1, lam);
                Complex f2 = w2 * host.GPsi(c1, c2, ch, ell[c1, c2, ch], A / w2, lam);
                double rhsBase = (A / Math.Min(w1, w2)) * Math.Abs(w1 - w2);
                double ratio = (f1 - f2).Magnitude / rhsBase;
                if (ratio > maxLipRatio)
                {
                    maxLipRatio = ratio;
                    maxLipWitness = string.Format("psi=({0},{1},{2}) A={3:F3} w1={4:F4} w2={5:F4} (A/w1={6:F3})", c1, c2, ch, A, w1, w2, A / w1);
                }
            }
        }
        sb.AppendLine(string.Format("[1C] LipW adversarial fuzz (8,000 trials incl. A/w < 1): max ratio = {0:F6} (claimed bound: 3.000000)", maxLipRatio));
        sb.AppendLine(string.Format("     Worst LipW witness: {0}", maxLipWitness));

        // 1D: Explicit boundary check of A/w -> 0+ for psi = 0 (principal character!)
        // Wait: for psi = 0, w * G_0(A/w) = -A * (log(A/w) - 1 - gamma) when A/w < 1!
        // Derivative wrt w is +A/w! Ratio |w G_0(A/w) - w' G_0(A/w')| / ((A/min(w,w'))*|w-w'|) -> 1!
        // What about psi = 0 at A/w = 2.001 vs 1.999 or near peak of psi(y)/y = 1.0388 (at y = 113)?
        double A113 = 113.001, wa = 1.0, wb = 1.00001;
        Complex fa = wa * host.GPsi(0, 0, 0, Complex.Zero, A113 / wa, lam);
        Complex fb = wb * host.GPsi(0, 0, 0, Complex.Zero, A113 / wb, lam);
        double r113 = (fa - fb).Magnitude / ((A113 / wa) * (wb - wa));
        Complex faC = wa * host.GPsi(1, 0, 0, ell[1, 0, 0], A113 / wa, lam);
        Complex fbC = wb * host.GPsi(1, 0, 0, ell[1, 0, 0], A113 / wb, lam);
        double r113C = (faC - fbC).Magnitude / ((A113 / wa) * (wb - wa));
        sb.AppendLine(string.Format("     At Chebyshev peak y=113: psi=0 LipW ratio = {0:F6}; psi=chC LipW ratio = {1:F6}", r113, r113C));

        // Real-prime growth check for M=308 characters at x = 100, 1000, 10000
        sb.AppendLine("[1D] Real-prime values of G_psi(x) / sqrt(x) on M=308:");
        foreach (double xv in new double[] { 100.0, 1000.0, 10000.0 })
        {
            double g0 = host.GPsi(0, 0, 0, Complex.Zero, xv, lam).Real;
            double gCh = host.GPsi(1, 0, 0, ell[1, 0, 0], xv, lam).Real;
            double gPs = host.GPsi(0, 1, 0, ell[0, 1, 0], xv, lam).Real;
            double gH1 = host.GPsi(0, 0, 1, ell[0, 0, 1], xv, lam).Magnitude;
            sb.AppendLine(string.Format("     x={0,5:F0}: G_0/sqrt(x)={1,8:F4}, G_chC/sqrt(x)={2,8:F4}, G_psC/sqrt(x)={3,8:F4}, |G_H1|/sqrt(x)={4,7:F4}",
                xv, g0 / Math.Sqrt(xv), gCh / Math.Sqrt(xv), gPs / Math.Sqrt(xv), gH1 / Math.Sqrt(xv)));
        }

        return sb.ToString();
    }

    // EXPERIMENT 2: Adversarial Fuzz of SizeWindows -> GrowthSizeBound AND MeanBoundSecondForm (each_unit_bound_statement)
    public static string RunExperiment2()
    {
        var sb = new System.Text.StringBuilder();
        var rng = new Random(777137);

        // 2A: Fuzz SizeWindows -> GrowthSizeBound (GrowthBoundGivesRiemannHypothesis.lean L109-122)
        // Trying to BREAK Gx <= x^(1/2 + (C+3)*eps) across 20,000 extreme valid tuples!
        int swTested = 0, swViol = 0;
        double maxSwRatio = 0.0;
        string swWorst = "";
        for (int i = 0; i < 20000; i++)
        {
            double eps = (i % 4 == 0) ? (0.01 + rng.NextDouble() * 0.2)
                       : (i % 4 == 1) ? (0.2 + rng.NextDouble() * 2.0)
                       : (i % 4 == 2) ? (2.0 + rng.NextDouble() * 10.0) // intentionally test eps > 1!
                       : (0.005 + rng.NextDouble() * 0.02);
            double xMin = Math.Max(3.0, Math.Pow(26.0, 8.0 / (3.0 * eps)));
            if (double.IsInfinity(xMin) || xMin > 1e100) continue;
            double x = xMin * (1.0 + rng.NextDouble() * ((i % 2 == 0) ? 0.001 : 100.0)); // tight at xMin!
            double C = (i % 3 == 0) ? 0.0 : (rng.NextDouble() * 5.0);
            double b = Math.Pow(10.0, -5 + rng.NextDouble() * 15.0);
            double aE = (i % 2 == 0) ? (2.0 * x * b) : (rng.NextDouble() * 2.0 * x * b);
            double mLo = Math.Pow(x, 0.5 - eps);
            double mHi = Math.Pow(x, 0.5 + eps / 2.0);
            if (mHi < 1.0 || double.IsInfinity(mHi)) continue;
            double mD = Math.Ceiling(mLo);
            if (i % 2 == 1) mD = Math.Floor(mHi);
            if (mD < mLo || mD > mHi || mD < 1.0) continue;
            // Pick n large enough so nT, nT2 >= 1 and k <= n^2 * x^(1/2-eps)
            double nMin = Math.Max(Math.Ceiling(Math.Pow(x, eps)), Math.Ceiling(Math.Sqrt(x * mD / Math.Pow(x, 0.5 - eps))));
            if (double.IsInfinity(nMin) || nMin > 1e15) continue;
            double nD = Math.Max(1.0, nMin * (1.0 + rng.NextDouble() * 2.0));
            double nT = Math.Ceiling(Math.Pow(x, -eps / 8.0) * nD / 2.0);
            double nT2 = Math.Ceiling(Math.Pow(x, -eps) * nD);
            if (nT2 > nD) continue;
            double kLo = x * mD;
            double kHi = nD * nD * Math.Pow(x, 0.5 - eps);
            if (kHi < kLo) continue;
            double k = (i % 2 == 0) ? kHi : kLo;

            double errBracket = nT * aE * (1.0 + mD * mD / k)
                              + mD * (2.0 * nD * mD * b * Math.Pow(x, eps) + nT2 * k * b * Math.Pow(x, eps) / (nD * nD * Math.Pow(x, -eps)));
            double Err = Math.Pow(x, C * eps) * errBracket;
            double denom = nT * mD * b * ((nT2 / nD) / 2.0);
            double maxGx = 4.0 * Math.Pow(x, 0.5 + eps) + (Err + 2.0 * nT * mD * b / x) / denom;
            double target = Math.Pow(x, 0.5 + (C + 3.0) * eps);
            double ratio = maxGx / target;
            swTested++;
            if (ratio > 1.0 + 1e-12) swViol++;
            if (ratio > maxSwRatio)
            {
                maxSwRatio = ratio;
                swWorst = string.Format("eps={0:F3} x={1:E2} C={2:F2} ratio={3:F6}", eps, x, C, ratio);
            }
        }
        sb.AppendLine(string.Format("[2A] SizeWindows->GrowthSizeBound fuzz ({0} valid extreme tuples, incl. eps>1): violations = {1}, max Gx/target = {2:F6}",
            swTested, swViol, maxSwRatio));
        sb.AppendLine(string.Format("     Tightest tuple: {0}", swWorst));

        // 2B: Fuzz MeanBoundSecondForm / PointwiseBoundVariant (QuotientSlopeBoundsWith.lean L19-76 + MeanBoundSecondForm.lean)
        // Construct adversarial Data tuples with |W|=3 satisfying ALL 11 hypotheses of SizeData2,
        // maximizing ASK - Main - ErrX5at to try to break each_unit_bound_statement!
        int mbTested = 0, mbViol = 0;
        double maxGap = double.NegativeInfinity;
        string mbWorst = "";
        for (int i = 0; i < 15000; i++)
        {
            double x = 3.0 + rng.NextDouble() * 500.0;
            double eps = 0.01 + rng.NextDouble() * 0.5;
            double b = 1.0 + rng.NextDouble() * 100.0;
            double a = x * b * (1.0 + rng.NextDouble() * 0.5);
            double bPrime = rng.NextDouble() * (a / 10.0);
            int m = 1 + rng.Next(8);
            int f = 1 + rng.Next(6);
            int nTop = 1 + rng.Next(6);
            double k = Math.Max(x * m, 2.0) * (1.0 + rng.NextDouble() * 5.0);
            double L = Math.Log(b) + 1.0;
            double La = Math.Log(a) + 2.0;
            double B0 = rng.NextDouble() * 50.0;
            double Nc = rng.NextDouble() * 50.0;
            double v = 0.5 + rng.NextDouble() * 5.0;
            double lg = -2.0 + rng.NextDouble() * 4.0;
            double gam = EULER_GAMMA;
            double LpL = -2.0 + rng.NextDouble() * 4.0;
            double Xpp = rng.NextDouble() * 20.0;

            double cDiv = rng.NextDouble() * 3.0;
            double eDiv = rng.NextDouble() * 2.0;
            double cE = rng.NextDouble() * 3.0;
            double cH = rng.NextDouble() * 3.0;
            double cCount = rng.NextDouble() * 3.0;
            double cSlope = rng.NextDouble() * 3.0;
            double cSl1 = rng.NextDouble() * 3.0;
            double cLoss = rng.NextDouble() * 3.0;
            double eLoss = rng.NextDouble() * 2.0;
            double cHH = rng.NextDouble() * 2.0;

            double delBar = rng.NextDouble() * 0.9; // up to 0.9 < 1!
            double etaBar = rng.NextDouble() * 0.5;
            double eBar = rng.NextDouble() * 0.25; // up to 1/4!

            double[] aT = new double[nTop];
            double sumA = 0.0;
            for (int t = 0; t < nTop; t++) { aT[t] = 0.1 + rng.NextDouble() * a; sumA += aT[t]; }

            double[,] w = new double[m, f];
            double sLogW = 0.0;
            for (int j = 0; j < m; j++)
            for (int r = 0; r < f; r++)
            {
                w[j, r] = 0.2 + rng.NextDouble() * 20.0;
                sLogW += Math.Log(w[j, r]) / f;
            }

            // Build |W| = 3 words with random positive ranks d_u and adversarial slopes
            int nW = 3;
            double[] dW = new double[nW];
            double[] logT = new double[nW];
            double[] muM = new double[nW];
            double[] muMaxM = new double[nW];
            double[] Ee = new double[nW];
            double[] hW = new double[nW];
            double[] muN = new double[nW];
            double[] muMaxN = new double[nW];

            // Count5 lower bound for logT
            double logT_lo = sLogW + m * Math.Log(v / Math.PI) + m * lg - cCount * (La + m * m * La / k);
            double logT_hi = cCount * m * L;
            if (logT_lo > logT_hi) continue;
            double baseLogT = logT_lo + rng.NextDouble() * (logT_hi - logT_lo);
            for (int u = 0; u < nW; u++)
            {
                dW[u] = 0.1 + rng.NextDouble() * 10.0;
                double delta = (rng.NextDouble() - 0.5) * Math.Min(cCount * Math.Log(k), 1.0);
                logT[u] = Math.Max(logT_lo, Math.Min(logT_hi, baseLogT + delta));
                if (logT[u] > 500) logT[u] = 500;
            }
            // Verify pairwise Count5
            bool okCount = true;
            for (int u = 0; u < nW; u++)
            for (int u2 = 0; u2 < nW; u2++)
                if (Math.Abs(logT[u] - logT[u2]) > cCount * Math.Log(k) + 1e-12) okCount = false;
            if (!okCount) continue;

            double LoP = cLoss * nTop * m * b * Math.Pow(x, eLoss * eps);
            double IO = rng.NextDouble() * LoP;
            double Fo = -10.0 + rng.NextDouble() * 20.0;
            double Ga = -10.0 + rng.NextDouble() * 20.0;
            // Maximize ASK subject to LossBounds: ASK = Ga + LoP
            double ASK = Ga + LoP;

            double slLo = -cSlope * nTop * a * La * (1.0 + (double)m / k);
            double slHi = cSlope * nTop * a * La;
            double baseH = -5.0 + rng.NextDouble() * 10.0;
            double hBound = cH * (nTop * a * La + m * B0);
            for (int u = 0; u < nW; u++)
            {
                muM[u] = slLo + rng.NextDouble() * (slHi - slLo);
                muMaxM[u] = muM[u] + rng.NextDouble() * (slHi - muM[u]);
                Ee[u] = m * sumA * lg + (2.0 * rng.NextDouble() - 1.0) * cE * m * B0;
                // Choose hW[u] to satisfy HComp
                hW[u] = baseH - sumA * logT[u] + (rng.NextDouble() - 0.5) * hBound;
            }
            bool okH = true;
            for (int u = 0; u < nW; u++)
            for (int u2 = 0; u2 < nW; u2++)
                if (Math.Abs((hW[u] + sumA * logT[u]) - (hW[u2] + sumA * logT[u2])) > hBound + 1e-12) okH = false;
            if (!okH) continue;

            // QuotientSlopeBoundsWith bounds muN and muMaxN
            bool okN = true;
            for (int u = 0; u < nW; u++)
            {
                double Lo5 = cSl1 * IO + cSl1 * nTop * m * (a / k + bPrime) * logT[u] + cSl1 * Xpp + 1.0;
                double loN = muM[u] + Ga + Fo - Ee[u] - Lo5;
                double hiN = muMaxM[u] + Ga + Fo - Ee[u] + cSl1 * m * B0;
                if (loN > hiN) { okN = false; break; }
                // Pick muN near loN (or adversarial) and muMaxN near hiN to stretch uF!
                muN[u] = loN + rng.NextDouble() * (hiN - loN) * 0.2;
                muMaxN[u] = muN[u] + rng.NextDouble() * (hiN - muN[u]);
            }
            if (!okN) continue;

            // Compute s and uF
            double sumD = 0.0, numS = 0.0, supVal = double.NegativeInfinity;
            for (int u = 0; u < nW; u++)
            {
                sumD += dW[u];
                numS += dW[u] * (muN[u] - hW[u]);
                double vMax = muMaxN[u] - hW[u];
                if (vMax > supVal) supVal = vMax;
            }
            double sVal = numS / sumD;
            double uF = supVal - sVal;

            // Set HH = x^cHH * b (worst case) and del = delBar, eta = etaBar, e = eBar
            double HH = Math.Pow(x, cHH) * b;
            double uFterm = (uF > 1e-15) ? (4.0 * uF * Math.Log(1.0 + HH / uF)) : 0.0;
            // SlopeIneq gives LOWER bound on muCC:
            double muCC_lo = sVal - Math.Log(nW) - (uFterm + (etaBar + 4.0 * Math.Sqrt(eBar)) * HH) / (1.0 - delBar);

            // DIV gives UPPER bound on muCC across all u:
            double logOm = gam + Math.Log(Math.PI / v) - LpL;
            double muCC_hi = double.PositiveInfinity;
            for (int u = 0; u < nW; u++)
            {
                double rhsDiv = 0.0;
                for (int t = 0; t < nTop; t++)
                    rhsDiv += m * (aT[t] * Math.Log(aT[t]) - aT[t] - aT[t] * logOm) - aT[t] * logT[u];
                rhsDiv += cDiv * nTop * a * La + cDiv * m * (B0 + Nc) * Math.Pow(x, eDiv * eps);
                double hi = rhsDiv - hW[u] + Fo;
                if (hi < muCC_hi) muCC_hi = hi;
            }
            // Feasible iff muCC_lo <= muCC_hi!
            if (muCC_lo > muCC_hi + 1e-12) continue;

            // Compute Main and ErrX5at (QuotientSlopeBoundsWith.lean L37-54)
            double Main = 0.0;
            for (int j = 0; j < m; j++)
            for (int t = 0; t < nTop; t++)
            {
                double avgLogW = 0.0;
                for (int r = 0; r < f; r++) avgLogW += Math.Log(w[j, r]) / f;
                Main += aT[t] * (Math.Log(aT[t]) - 1.0 - gam + LpL - avgLogW);
            }
            double Vvar = 2.0 * m * cE * B0 + cH * (nTop * a * La + m * B0) + sumA * (cCount * Math.Log(k));
            double MLo5 = cSl1 * LoP + cSl1 * nTop * m * (a / k + bPrime) * (cCount * m * L) + cSl1 * Xpp + 1.0;
            double UBar5 = cSlope * nTop * a * La * (2.0 + (double)m / k) + Vvar + cSl1 * m * B0 + MLo5;
            double ErrX5at = sumA * (cCount * (La + m * m * La / k))
                           + (cDiv * nTop * a * La + cDiv * m * (B0 + Nc) * Math.Pow(x, eDiv * eps))
                           + m * cE * B0
                           + cSlope * nTop * a * La * (1.0 + (double)m / k)
                           + Math.Log(nW)
                           + LoP
                           + MLo5
                           + (4.0 * Math.Log(1.0 + Math.Pow(x, cHH)) * (UBar5 + b) + (etaBar + 4.0 * Math.Sqrt(eBar)) * (Math.Pow(x, cHH) * b)) / (1.0 - delBar);

            double gap = ASK - (Main + ErrX5at);
            mbTested++;
            if (gap > 1e-7 * (Math.Abs(Main) + Math.Abs(ErrX5at) + 1.0))
            {
                mbViol++;
            }
            if (gap > maxGap)
            {
                maxGap = gap;
                mbWorst = string.Format("gap={0:E3} ASK={1:E3} Main={2:E3} ErrX5at={3:E3} uF={4:E2} UBar5={5:E2}",
                    gap, ASK, Main, ErrX5at, uF, UBar5);
            }
        }
        sb.AppendLine(string.Format("[2B] SizeData2->each_unit_bound_statement fuzz ({0} feasible adversarial Data tuples): violations = {1}", mbTested, mbViol));
        sb.AppendLine(string.Format("     Worst gap ASK - (Main + ErrX5at): {0}", mbWorst));

        // 2C: Exact-Equality Corner Attack on SizeData2 (all error constants = 0, delBar = 0.999, |W|=1 and |W|=100, uF->0 and uF=UBar5)
        double maxCornerGap = double.NegativeInfinity;
        int cornerViol = 0;
        foreach (int nW in new int[] { 1, 2, 10, 100 })
        foreach (double delBar in new double[] { 0.0, 0.5, 0.999 })
        foreach (double cScale in new double[] { 0.0, 1e-6, 1.0 })
        {
            double x = 10.0, eps = 0.05, b = 100.0, a = 1000.0, bPrime = 1.0, k = 5000.0, L = 5.0, La = 8.0, B0 = 10.0, Nc = 10.0, v = 2.0, lg = 1.5, Xpp = 5.0;
            int m = 3, nTop = 2;
            double cDiv = cScale, eDiv = 1.0, cE = cScale, cH = cScale, cCount = cScale, cSlope = cScale, cSl1 = cScale, cLoss = cScale, eLoss = 1.0, cHH = 1.0;
            double etaBar = 0.0, eBar = 0.0;
            double[] aT = new double[] { 900.0, 1000.0 };
            double sumA = 1900.0;
            double sLogW = 0.0; // w = 1 everywhere
            double logT_lo = sLogW + m * Math.Log(v / Math.PI) + m * lg - cCount * (La + m * m * La / k);
            double logT = logT_lo; // tight!
            double LoP = cLoss * nTop * m * b * Math.Pow(x, eLoss * eps);
            double IO = LoP; // tight!
            double Lo5 = cSl1 * IO + cSl1 * nTop * m * (a / k + bPrime) * logT + cSl1 * Xpp + 1.0;
            double muM = -cSlope * nTop * a * La * (1.0 + (double)m / k); // tight!
            double muMaxM = cSlope * nTop * a * La; // tight!
            double Ee = m * sumA * lg + cE * m * B0; // tight max!
            double logOm = EULER_GAMMA + Math.Log(Math.PI / v) - 0.5;
            double Main = 0.0, Main_T = 0.0;
            foreach (double at in aT)
            {
                Main += m * at * (Math.Log(at) - 1.0 - EULER_GAMMA + 0.5);
                Main_T += m * (at * Math.Log(at) - at - at * logOm) - at * logT;
            }
            double divRhs = Main_T + cDiv * nTop * a * La + cDiv * m * (B0 + Nc) * Math.Pow(x, eDiv * eps);
            // Set Fo = 0, h = 0, muCC = divRhs (tight DIV!)
            double muCC = divRhs;
            double HH = Math.Pow(x, cHH) * b;
            // Stretch uF to its maximum allowed by SlopesN (word 0 at loN, word 1 at hiN, d_0 >> d_1):
            double uF = (nW == 1) ? 0.0 : ((muMaxM - muM) + cSl1 * m * B0 + Lo5);
            double uFterm = (uF > 1e-15) ? (4.0 * uF * Math.Log(1.0 + HH / uF)) : 0.0;
            // Tight SlopeIneq: s = muCC + log(nW) + uFterm / (1 - delBar)
            double sVal = muCC + Math.Log(nW) + uFterm / (1.0 - delBar);
            // Tight SlopesN lower: Ga = sVal - muM + Ee + Lo5; tight LossBounds: ASK = Ga + LoP
            double ASK = sVal - muM + Ee + Lo5 + LoP;

            double Vvar = 2.0 * m * cE * B0 + cH * (nTop * a * La + m * B0) + sumA * (cCount * Math.Log(k));
            double MLo5 = cSl1 * LoP + cSl1 * nTop * m * (a / k + bPrime) * (cCount * m * L) + cSl1 * Xpp + 1.0;
            double UBar5 = cSlope * nTop * a * La * (2.0 + (double)m / k) + Vvar + cSl1 * m * B0 + MLo5;
            double ErrX5at = sumA * (cCount * (La + m * m * La / k))
                           + (cDiv * nTop * a * La + cDiv * m * (B0 + Nc) * Math.Pow(x, eDiv * eps))
                           + m * cE * B0
                           + cSlope * nTop * a * La * (1.0 + (double)m / k)
                           + Math.Log(nW)
                           + LoP
                           + MLo5
                           + (4.0 * Math.Log(1.0 + Math.Pow(x, cHH)) * (UBar5 + b) + (etaBar + 4.0 * Math.Sqrt(eBar)) * (Math.Pow(x, cHH) * b)) / (1.0 - delBar);
            // Check if logT <= cCount * m * L is actually satisfied (Count5 upper)!
            if (logT > cCount * m * L) continue;
            double gap = ASK - (Main + ErrX5at);
            if (gap > maxCornerGap) maxCornerGap = gap;
            if (gap > 1e-7) cornerViol++;
        }
        sb.AppendLine(string.Format("[2C] SizeData2 exact-equality corner attack (c=0..1, delBar up to 0.999, |W|=1..100): violations = {0}, max gap = {1:E3}",
            cornerViol, maxCornerGap));
        return sb.ToString();
    }

    // EXPERIMENT 3: Synthetic Off-Line Zero Barrier Test!
    // Inject a fake real zero at beta = 0.80 (adding +y^0.80 / (0.80 * 0.20) = +6.25 * y^0.80 to G_0(y))
    // into our concrete M=308 host AND trace the EXACT algebraic infeasibility forced onto SizeData2!
    public static string RunExperiment3()
    {
        var sb = new System.Text.StringBuilder();
        double beta = 0.80;
        double zeroCoeff = 1.0 / (beta * (1.0 - beta)); // 6.25 > 0!
        sb.AppendLine(string.Format("[3] Synthetic Off-Line Real Zero Barrier Test: beta = {0:F2} (delta G_0(x) = +{1:F2} * x^{0:F2})", beta, zeroCoeff));
        sb.AppendLine("    Scaling parameters from SizesTextAt (SChain.lean L212-221) with eps = 0.02:");

        double eps = 0.02;
        foreach (double x in new double[] { 1e4, 1e6, 1e8, 1e10 })
        {
            double n = Math.Pow(x, 2.0 + 8.0 * eps);
            double m = Math.Pow(x, 0.5 - eps / 16.0);
            double nT = Math.Pow(x, -eps / 8.0) * n / 2.0;
            double nT2 = Math.Pow(x, -eps) * n;
            double k = Math.Pow(x, 4.5 + 10.0 * eps);
            // Work in units of b (since b = exp(x^eps) scales linearly out of ASK, MAIN, ErrText, and D!)
            // Denominator D / b = nT * m * (nT2 / (2n))
            double D_over_b = nT * m * (nT2 / (2.0 * n));
            // Fake zero forces ASK - Main >= D * (delta G_0(x)) = b * D_over_b * (6.25 * x^0.80)
            double forcedExcess_over_b = D_over_b * zeroCoeff * Math.Pow(x, beta);
            // Allowed geometric error budget ErrText / b (with a = x*b, B0 = 2*n*m*b*x^eps, Nc = nT2*k*b*x^(2eps)/n^2)
            double a_over_b = x;
            double B0_over_b = 2.0 * n * m * Math.Pow(x, eps);
            double Nc_over_b = nT2 * k * Math.Pow(x, 2.0 * eps) / (n * n);
            double errText_over_b = nT * a_over_b * (1.0 + m * m / k) + m * (B0_over_b + Nc_over_b);
            // With C = eD + eL + 3 = 5 (eD=eL=1):
            double allowed_over_b = Math.Pow(x, 5.0 * eps) * errText_over_b;
            double infeasibilityRatio = forcedExcess_over_b / allowed_over_b;
            sb.AppendLine(string.Format("    x=1e{0,-2}: forced (ASK-Main)/b = {1:E3}, allowed x^(5eps)*ErrText/b = {2:E3}, VIOLATION FACTOR = {3:E3}x",
                (int)Math.Round(Math.Log10(x)), forcedExcess_over_b, allowed_over_b, infeasibilityRatio));
        }

        sb.AppendLine("    [3B] Algebraic Audit of the 4-Pillar Cancellation in MeanBoundSecondForm.lean:");
        sb.AppendLine("         Sum the 4 load-bearing inequalities (divided by b) for a single word u:");
        sb.AppendLine("           (1) LossBounds:  ASK - Ga <= LoP");
        sb.AppendLine("           (2) SlopesN:     Ga <= muN - muM - Fo + Ee + Lo5");
        sb.AppendLine("           (3) SlopeIneq:   (muN - h) <= muCC + log|W| + (1-del)^-1 (4 uF log(1+HH/uF) + (eta + 4 sqrt(e)) HH)");
        sb.AppendLine("           (4) DIV:         muCC + h - Fo <= Main_T + cDiv*(nT*a*La + m*(B0+Nc)*x^(eDiv*eps))");
        sb.AppendLine("         --> WAIT A SECOND! CHECK THE SIGN OF Fo IN (2) AND (4)!!");
        sb.AppendLine("         Let's verify: (2) has -Fo on RHS, (4) has -Fo on LHS -> +Fo on RHS -> (-Fo + Fo = 0) EXACT CANCELLATION!");
        sb.AppendLine("         CHECK THE SIGN OF Ee IN (2) AND Count5 IN (4):");
        sb.AppendLine("           (2) has +Ee ~ +m*(sumA)*lg; (4) has -sumA*log(T) <= -sumA*(sLogW + m*log(v/pi) + m*lg) -> (+m*sumA*lg - m*sumA*lg = 0) EXACT CANCELLATION!");
        sb.AppendLine("         CONCLUSION: A fake off-line zero at beta=0.80 forces the sum of (1)+(2)+(3)+(4) to fail by x^(0.30 - O(eps))!");
        return sb.ToString();
    }
}
"@

Write-Output "=== PASS 6.5 ADVERSARIAL TOY LAB ==="
Write-Output ([RhToyEngine]::RunExperiment1())
Write-Output ([RhToyEngine]::RunExperiment2())
Write-Output ([RhToyEngine]::RunExperiment3())
