# Alpöge 的 Dirichlet 广义黎曼猜想：证明思路

Lean 源码固定于 `371a1a26d5e17f604428e3a8ce6ce341cf517434`。它陈述的结论是，Dirichlet $L$ 函数在开临界带 $0<\Re s<1$ 内的零点都满足 $\Re s=1/2$。路线先在任意靠后的整段窗口上控制一个正权平滑和，再以极点矛盾排除右半带的零点。本文短述这一推导及其所需输入。 [原始命题][theorem] · [根入口][root] · [主链调用][basis]

## 1. 平滑和与晚窗

固定一个本原特征 $\psi$。令 $\mathcal X_\psi$ 为 $\psi$ 各幂所对应的本原特征的集合，$o=\operatorname{ord}(\psi)$，$\mathbf1$ 为模 $1$ 的平凡特征。对 $x\ge1$，以 $\Lambda(n)$ 表示 von Mangoldt 函数，$\gamma_E$ 表示欧拉常数，写
$$
\begin{aligned}
S_\chi(x)&=\sum_{1\le n\le x}\Lambda(n)\chi(n)(x/n-1),\\
G_\chi(x)&=
\begin{cases}
S_{\mathbf1}(x)-x\log x+(1+\gamma_E)x,&\chi=\mathbf1,\\
S_\chi(x)+x\,L'(1,\chi)/L(1,\chi),&\chi\ne\mathbf1,
\end{cases}\\
G_{\mathcal L}(x)&=G_{\mathbf1}(x)+\frac{1}{3o+1}
                   \sum_{\chi\in\mathcal X_\psi\setminus\{\mathbf1\}}\Re G_\chi(x).
\end{aligned}
$$
这里 $\mathcal L$ 是源码中的循环等级，$\psi$ 本身被保留。算术部分的目标是对每个固定 $\psi$ 建立
$$
\begin{gathered}
\exists\varepsilon_0>0\quad\forall\,0<\varepsilon<\varepsilon_0\quad
\forall\,Y_0\ge1\quad\exists\,Y\ge Y_0,\\[-2pt]
\forall x\in[Y,Y^{3/2}],\qquad G_{\mathcal L}(x)\le x^{1/2+9\varepsilon}.
\end{gathered}\tag{1}
$$
$\varepsilon$ 固定后，同一个辅助数据族提供所有这些晚窗。 [`Gchi` 与 `Gm`][sum] · [`Level.cyc`][cyc]、[权重][wt] · [`ChebyshevInequalityAtWindowScale`][winq]

## 2. 整段窗口的来源

Theta 提升给出 Galois 局部整体相容数据。由此进入的上同调支线在给定 $0<\varepsilon<1/52$ 和层函数 $2^{e(t)}\in[t^{2+8\varepsilon},2t^{2+8\varepsilon}]$ 后，固定 $J\ge1$。取足够大的 $X$，先在尺度 $X^{1/J}$ 选辅助素数 $q,d$，再取 $[W,W^2]\subset[X^{1/J},X]$。对每个 $t\in[W,W^2]$，相应数域在 $\lfloor t^{401}\rfloor$ 截断下的加权上同调长度和至多 $\exp(t^\varepsilon/2)$。整段区间来自对数尺度上避开有限个异常指数，异常集的基数界在取 $X$ 前固定。 [Galois 数据][lift]、[`vwin_of_row`][vrow]、[`of_four_alt`][count] · [`VWinAt`][vwin] · [`thmBab_of`][avoid]、[`window1`][wnd]

辅助数域、特征群和分歧资料构成宿主。其有限群的阶为 $c2^e$，$c\ge1$ 固定。令 $k=c^{1/(2+8\varepsilon)}$，取 $Y=kW$。只需令 $X^{1/J}\ge\max(Y_0,k^3,k^{400})$ 并超过择素数的阈值，就有 $Y^{3/2}\le W^2$。每个 $x\in[Y,Y^{3/2}]$ 都用原尺度 $t=x/k$ 的数据，且 $x^{400}\le t^{401}$、$t^\varepsilon\le x^\varepsilon$，所需长度界随之转移。承载这些数域与局部资料的尺度集合原样进入所选数据族。择素数用到的平方根型界针对 $q,d$ 的非平凡二次扭曲，显式公式中需另行估计的特征由此获得误差界。 [`fieldChi`][field]、[`winPairs`][scale] · [逐点宿主预算][supply] · [`exists_famP_of_kits`][kit] · [`PairGood`][pb]、[`pairEx`][pairs]、[`boundedTw_key`][filter]

## 3. 从 theta 配对到误差上界

在局部 Weil 模型匹配与相应的可积性条件下，两侧 theta 积分相差统一的非零因子。主链用此比较构造相容的测试向量和求值网格。局部条件、余体积界和定号与不定号实现的相容性，使这些行列数据可用于同一算术配对。对其中每个索引 $u$，若配对在有限处 $v$ 的估值至少是 $\sigma_v$，源格作有限支撑的移位，局部乘以估值 $-\tau_v$ 的标量，其中 $\tau_v\le\lceil\sigma_v\rceil$。配对因而在各处取整。由列格的局部识别得到算术格映射 $B_u:N'_u\to R^\vee$。整除预算使用上一节的上同调长度界。 [Eisenstein 与 Siegel–Weil 入口][K] · [`twisted_theta_integrals_agree`][tw] · [行数据装配][row]、[余体积供应][cov]、[`wire4F_alt`][geo] · [局部整除条件][adm]、[局部估值][dv]、[`divisor_into_dual_shift`][int]、[`divinN_of_hypV`][vdiv]

在固定尺度 $x$ 和一个宿主类，令 $\mu$ 为平均 Arakelov 斜率，$h_u$ 为 $B_u$ 的高度上界。以 $W_*$ 记该类的有限索引集，$s_*$ 为 $\mu(N'_u)-h_u$ 的秩加权均值。整除侧控制 $\mu(R^\vee)+h_u-F_o$，其中 $F_o$ 是归一化修正。结合商格斜率和计数比较得到左侧。框架侧用 Bost 型不等式控制像的最小斜率，使源格中扣除高度后仍高于阈值的部分进入目标的 Harder–Narasimhan 过滤。框架控制由此遗漏的秩，对阈值积分得到右侧
$$
G_a+\mu(R^\vee)-\mathrm{Main}-E_{\rm ar}
 \ \le\ s_*\ \le\
\mu(R^\vee)+\log|W_*|+E_{\rm fr}.
\tag{2}
$$
$G_a$ 是计数的中间量，$E_{\rm ar}$ 吸收商格与整除误差，$E_{\rm fr}$ 是框架比较的损失。两边逐类使用同一度量下的格和配对。消去 $\mu(R^\vee)$ 并计入 $\mathrm{ASK}-G_a$ 的损失界 $E_{\rm loss}$，便有 $\mathrm{ASK}-\mathrm{Main}\le E_{\rm ar}+E_{\rm fr}+\log|W_*|+E_{\rm loss}$。 [`LinkDIV_at`][hdiv] · [`s_lower5`][s0] · [`frame_at_of`][fr]、[秩积分][b] · [共同记录][same]、[同一格数据][align] · [`Ga_bound5`][s1]、[计数上界][cnt]

有限 Fourier 展开以 Frobenius 的惯性陪集平均作系数，把计数超额识别为字符和误差。归一化中出现 $x/m$ 与 $m$，秩参数取在 $[x^{1/2-\varepsilon},x^{1/2+\varepsilon/2}]$。密度与误差预算给出 $G_{\mathcal L}(x)\le x^{1/2+(e_D+e_L+6)\varepsilon}+\Sigma_A(x)$，其中非保留特征的误差 $\Sigma_A(x)\le4o\,x^{1/2+\varepsilon}$。整除和损失的指数预算取 $(e_D,e_L)=(2,0)$。令 $x^\varepsilon\ge1+4o$，即得所需指数。整除、框架与显式公式条件在选定的同一族成立，最终的字符数据和误差界使用同一参考宿主。把整段窗口置于共同阈值之后即得 (1)。 [`ch_balance`][frou]、[`ch_top`][ch] · [秩选择][rnk]、[归一化][sz] · [`ch_core`][chcore]、[保留项识别][matchsum]、[辅助误差][minus]、[`core_gm`][core]、[指数实参][pars] · [共同选族][design]、[同一宿主][eSame]、[窗口合用][en]

## 4. 单侧 Landau 与函数方程

若保留特征有零点 $\rho$ 满足 $1/2<\Re\rho<1$，选 $1/2<\theta<\Re\rho$，再取足够小的 $\varepsilon>0$ 使 $9\varepsilon\le\theta-1/2$。令 $u=\log x$、$U=\log Y$，则 $g(u)=G_{\mathcal L}(e^u)$ 在任意靠后的 $[U,3U/2]$ 上有非负包络 $e^{\theta u}$。其拉普拉斯变换 $\Phi(s)$ 中，对数导数的因子为 $-1/[s(s-1)]$，修正项使 $s=1$ 处的奇点可去。取实部对应特征与共轭特征的平均，所以在 $\rho$ 处的留数为
$$
-\frac{m_\rho}{\rho(\rho-1)},\qquad
m_\rho=\frac12\sum_{\chi\in\mathcal X_\psi}a_\chi
       \bigl(\operatorname{ord}_\rho L_\chi+\operatorname{ord}_\rho L_{\bar\chi}\bigr)>0,
$$
其中 $a_\chi$ 是第 1 节的正权。极点不会相消，实极点的留数为正。 [阈值选择][eps]、[`formB`][form] · [变换][mel]、[`poleData_abstract`][aux] · [留数与符号][res]

令 $A_k(s)=(-1)^k\Phi^{(k)}(s)/k!$。在实部为 $\sigma>2$ 的直线上，三角不等式把 $|A_k(\sigma+i\gamma)|+\Re A_k(\sigma)$ 控制在 $2g_+=|g|+g$ 的加权矩以下。取 $k=\lceil5\sigma U/4\rceil$，窗内用正包络，窗外用平滑和的粗界 $|g(u)|\ll e^{2u}$ 控制尾部。于是存在固定的 $\sigma,C$，对任意 $\eta>0$ 可取任意大的 $U$ 及相应的 $k\ge U$，使每个 $\gamma\in\mathbb R$ 都满足
$$
 |A_k(\sigma+i\gamma)|+\Re A_k(\sigma)
 \le C e^{\eta U}(\sigma-\theta)^{-k}.
$$
设所选展开中心到极点的距离为 $d$。Cauchy 估计给这个组合的下界 $c\,d^{-k}-M r^{-k}$，其中 $c>0$、$0<d<r\le\sigma-\theta$。实中心情形由正留数给出实部主项。复中心情形孤立较近的极点，并用实中心的无极点圆盘控制补项。取 $0<\eta<\log(r/d)$，再令 $U\to\infty$，两界矛盾。 [窗外矩尾][tail] · [单侧矩界][coeff] · [极点择取与矛盾][lcon]

这排除了所有本原特征在开带右半部的零点。本原完成函数的函数方程把 $L(s,\chi)=0$ 送到 $L(1-s,\bar\chi)=0$，两侧伽马因子在开带内有限且非零，故左半部也无零。若 $\chi_*$ 是诱导 $\chi$ 的本原特征，则 $L(s,\chi)$ 由 $L(s,\chi_*)$ 乘有限个因子 $1-\chi_*(p)p^{-s}$ 得到。这些因子在 $\Re s>0$ 均非零。 [`lemmaL`][lz] · [`prim_reflect` 与 `strip`][fn] · [Euler 因子][eu]

**核对范围。** 已从根入口静态追到上述装配、消项、窗口与解析判据的实际调用。底层自守和局部几何供应、上同调分情形计数、框架缺陷与择素数的均方估计仍按具名输入引用，未独立验证其传递依赖。本说明基于固定源码文本，未作 Lean 内核验收。 [主链装配][use] · [择素数的均方输入][screen]

[theorem]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Statements.lean#L6-L16
[root]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Main.lean#L4-L12
[basis]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L7-L11
[sum]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean#L10-L36
[cyc]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L105-L124
[wt]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L32-L38
[winq]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L23-L32
[lift]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean#L1-L6
[vrow]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean#L4-L5
[count]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/HVCore.lean#L18-L22
[vwin]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L39-L49
[avoid]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/ThmBabOf.lean#L75-L99
[wnd]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window1.lean#L6-L42
[field]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/FieldChi.lean#L20-L26
[scale]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean#L9-L81
[supply]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean#L125-L135
[kit]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsFamPOfKits.lean#L159-L170
[pb]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean#L18-L30
[pairs]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean#L112-L169
[filter]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean#L5-L31
[K]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean#L14-L27
[tw]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean#L17-L41
[row]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L44-L68
[cov]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolSlim2Use.lean#L16-L22
[geo]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Wire4F.lean#L58-L91
[adm]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ClosedFamilyAdmissibleTwistLink.lean#L13-L31
[dv]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean#L633-L641
[int]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean#L720-L730
[vdiv]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean#L79-L130
[hdiv]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L77-L89
[s0]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L50-L66
[fr]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean#L538-L600
[b]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L194-L386
[same]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean#L169-L209
[align]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean#L63-L82
[s1]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L105-L160
[cnt]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L175-L197
[frou]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean#L200-L260
[ch]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L37-L72
[rnk]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsRanksRankValFrame.lean#L45-L100
[sz]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L507-L535
[chcore]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L343-L351
[matchsum]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean#L61-L80
[minus]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean#L38-L60
[core]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L51-L74
[pars]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean#L48-L55
[design]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean#L23-L31
[eSame]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean#L17-L25
[en]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean#L16-L34
[eps]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L68-L81
[form]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean#L8-L19
[mel]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean#L116-L129
[aux]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L22-L46
[res]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L338-L383
[tail]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauTails.lean#L80-L104
[coeff]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L40-L73
[lcon]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L166
[lz]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean#L13-L22
[fn]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L35-L73
[eu]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L7-L33
[use]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L810-L813
[screen]: https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean#L41-L56
