# 从 theta 积分配对到 Dirichlet L 函数的零点排除

固定一个本原 Dirichlet 特征 $\psi$。源码把它放在由其幂生成的一个有限特征族中，目标是排除这个族在 $\Re s>1/2$ 的零点。论证的算术部分估计一个带符号的平滑素数和。theta 配对提供可在局部和整体之间比较的测试数据，有限处的整除把同一个配对变成格映射，两个方向的斜率估计消去共同的对偶格斜率。所得上界只要在任意靠后的整段窗口成立，就能与零点在 Laplace 变换中产生的极点相矛盾。

以下说明据第一轮路线图改写，所引声明一律取自原仓库固定提交 `371a1a26d5e17f604428e3a8ce6ce341cf517434`。公开整理笔记固定在 `d0c39afd1fcb7b2cbd0fca390486cf29a51daafa`，用于导航。本文给出所读证明之间的推导，并在用到几何、表示论和算术供应时注明输入。 [第一轮源码路线图](PROOF-MAP.md) · [原始源码](https://github.com/leanprover-community/riemann-hypothesis/tree/371a1a26d5e17f604428e3a8ce6ce341cf517434) · [公开导航笔记](https://github.com/h-lu/riemann-hypothesis/blob/d0c39afd1fcb7b2cbd0fca390486cf29a51daafa/PROOF-MAP.md)

## 1. 要估计的平滑和

记 $\Lambda_{\rm vM}$ 为 von Mangoldt 函数，令
$$
\mathcal R_\chi(y)=\sum_{1\le n\le y}\Lambda_{\rm vM}(n)\chi(n)(y/n-1),\qquad y\ge1.
$$
模一平凡特征的误差是 $G_1(y)=\mathcal R_1(y)-y\log y+(1+\gamma)y$，其中 $\gamma$ 是欧拉常数。对非平凡特征，误差是 $G_\chi(y)=\mathcal R_\chi(y)+y\,L'(\chi,1)/L(\chi,1)$。取等级 $\mathcal L=\mathrm{Level.cyc}(\psi)$，保留 $\psi$ 的各幂所诱导的本原特征，包含 $\psi$ 和模一特征。若 $o=|\langle\psi\rangle|$，则模一项权重为 $1$，其余权重为 $(3o+1)^{-1}$。记合成的实值误差为 $G_{\mathcal L}(y)=\sum_\chi a_\chi\Re G_\chi(y)$。权重 $a_\chi>0$ 将在极点的留数计算中用到。 [`Gchi` 与 `CharFamily`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean#L10-L39) · [`Level.Gm` 的权重](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L30-L38) · [`Level.cyc` 与成员资格](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L105-L127) · [等级与解析族的识别 `level_family`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelFamily.lean#L27-L52)

固定 $\psi$ 后，算术部分需要建立
$$
\exists\varepsilon_0>0\ \forall\,0<\varepsilon<\varepsilon_0\ \forall\,Y_0\ge1\
\exists\,Y\ge Y_0\ \forall\,x\in[Y,Y^{3/2}],\qquad
G_{\mathcal L}(x)\le x^{1/2+9\varepsilon}. \tag{W}
$$
$\varepsilon$ 先选，随后选用一个满足该 $\varepsilon$ 的数据族。估计从依赖该族的阈值起，对其可用尺度逐点成立。窗口的作用是确保这批尺度包含任意靠后的整段区间。源码中窗口上界的一般指数为 $1/2+(e_D+e_L+7)\varepsilon$，实际取 $e_D=2,\ e_L=0$。 [`ChebyshevInequalityAtWindowScale` 与逐点上界](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L23-L32) · [`HasWindows`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean#L7-L15) · [`shape_closed_link_n_of_green` 的参数](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean#L48-L55)

## 2. Theta 提供匹配的测试数据

在一组满足配对条件的 Hermite 空间和 Hecke 特征上，两侧各有一个 Weil 模型。`LocalMatching` 为它们选取无穷处和有限处的线性商映射。多项式型测试向量的匹配意味着投到这些共同商的张量积后相等，平滑匹配再由逼近得到。`ThetaIntegralsAgree` 给出收敛与衰减、好有限处的余不变量条件，以及匹配积分的唯一非零比例常数。它还给出沿两条 theta 塔降低秩时比例常数的比较。 [商映射、`PolMatch` 和 `OneConst`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L425-L511) · [`LocalMatching` 与 `ThetaIntegralsAgree`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L559-L592)

在扭曲数据的版本里，固定相容的 Hermite 三元组、加法与 Hecke 特征、Haar 基本域和局部匹配。若 $p\Phi=p'\Phi'$ 是匹配投影的等式，且相应的第二个核可积，那么
$$
I_A(\Phi)=c\,I_B(\Phi'),\qquad c\ne0,
$$
其中 $c$ 对这组数据下的测试向量统一。证明先用有限处关系将 $\Phi'$ 换成一个适合积分比较的代表 $\Phi'_0$，投影保持相等，差 $\Phi'-\Phi'_0$ 的积分为零。主链使用的 `twisted_theta_integrals_agree` 在构造代表时把全局模型的比例常数与扭曲核的比例常数相乘。 [`twisted_theta_integrals_agree`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean#L17-L41) · [`thetaIntegrals_agree_of_integrable_kernel`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaIntegralsAgreeOfIntegrableKernel.lean#L65-L94)

要把积分比较用于整除，还需要泛函分离、局部因子和系数域输入。`test_vector_at_datum_of_join` 把扭曲匹配和收敛用于测试向量的行性质，再用扩域结果得到有理行测试。`evaluation_grid_of_join` 把相应的系数和传递关系组织成在大参数下可用的求值网格。组装定号侧数据时，取行函数与网格所需阈值的最大值，加入统一余体积界和局部行范数界，得到 `DefiniteSideCondition` 所要求的选择。它在余体积、满射、等距和整除相容等条件下，为同一个原始行列包提供 `RowsU`。`wire_sel_alt` 随后用选定实现的秩等式把几何行条件转成实际行条件，并识别基准秩 $D_0$。这给下节指定了要作整性比较的局部列格和双线性配对。 [`test_vector_at_datum_of_join`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TestVectorAtDatumOfJoin.lean#L20-L31) · [`evaluation_grid_of_join`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/EvaluationGridOfJoin.lean#L23-L44) · [`nonempty_hyps_definite_side_of_closed_bound`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L44-L68) · [`DefiniteSideCondition`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DefiniteSideCondition.lean#L25-L35) · [`wire_sel_alt`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/WireSel.lean#L34-L50)

这个 theta 接口由 `theoremK_head2` 调用球面构造 `closeSph` 给出。构造使用 Eisenstein 与 Siegel–Weil 输入、倍增积分的非零性、局部重数一和两端的比较。源码还在另一条支线上使用 theta 提升来供应 Galois 局部整体相容的行数据。`everyCharacter_of_row` 一方面把这条行数据传给 theta 及相关输入的装配，另一方面用它产生 `VWin`。后者经 `supplyChi` 供应窗口内的宿主数据，其中包括固定循环等级的特征估计和后面要用的 $\sqrt b$ 上同调预算。匹配和宿主供应在 `every_character_of_theta_integrals_local_matching` 与 `TopPlug` 的调用中合用。 [`theoremK_head2`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean#L14-L27) · [`closeSph` 的倍增和消失输入](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/CloseSph.lean#L105-L150) · [Galois 行的供应](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean#L1-L6) · [`everyCharacter_of_row`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L7-L11) · [`supplyChi`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean#L8-L16) · [theta 与 `VWin` 传入同一调用](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L810-L813) · [行数据导出 `VWin`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean#L4-L5) · [宿主输出 `HostExW`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean#L17-L23) · [`TopPlug`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean#L12-L18)

## 3. 局部整除怎样变成算术格映射

固定尺度 $x$ 和一个宿主类 $u_0$，以 $u$ 表示该类中的一个字，即构造里的一个有限索引。以 $K$ 表示配对的系数数域，$N_u$ 是平移前的源格，$R$ 是列侧格。要构造的是由双线性配对 $B_u(\phi,r)$ 决定的映射 $N'_u\to R^\vee$，其中 $R^\vee$ 由在 $R$ 上取 $\mathcal O_K$ 值的线性泛函组成。对每个有限处 $w$，取局部列数据 $M_w$ 及线性传递 $j_w$。需要的相容式为
$$
R_w=(j_w M_w)_w,\qquad
P_w(\phi,F)=\zeta_w B_u(\phi,j_w F),\qquad \zeta_w\ne0,\quad v_w(\zeta_w)=0.
$$
下标 $w$ 表示局部化。整除输入是对 $\phi\in N_u,\ F\in M_w$，$P_w(\phi,F)$ 为零或 $v_w(P_w(\phi,F))\ge\sigma_w$。`val2AllAtRF` 用 `adm2` 的整除数据及列的相容关系把下界传给实际配对。所用的局部指数由记录中的增益和损失换算到 $K$ 的估值单位后向下取整。 [`DivIntoDualShift` 的假设](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/QuotientMetricDivisors/DivIntoDualShift.lean#L127-L147) · [`val2AllAtRF`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/GroupLattices/ServJointF.lean#L84-L102) · [`shiftZ_sgFl`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/GroupLattices/JointServices/ShiftIdealSgFl.lean#L14-L45) · [`DivisionPackageFace.wordFacts`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean#L633-L641)

给定有限支撑的整数移位 $\tau_w$，一般定理只需 $\tau_w\le\lceil\sigma_w\rceil$。令
$$
N'_u=\Big(\prod_w\mathfrak p_w^{-\tau_w}\Big)N_u.
$$
在 $w$ 处这是用估值 $-\tau_w$ 的标量 $a_w$ 乘源格。若 $\phi'\in N'_u$，可写成 $t\phi'=a_w\phi$，其中 $\phi\in N_u$，$t$ 在 $w$ 处为单位。固定 $F$ 后，线性性给出 $tP_w(\phi',F)=a_wP_w(\phi,F)$。非零值的估值是整数，故 $v_w(P_w(\phi,F))\ge\lceil\sigma_w\rceil$，从而新配对在 $w$ 处取整。由列格的局部化等式和 $\zeta_w$ 为单位，整性传给 $B_u(\phi',r)$，$r\in R_w$。最后 $\bigcap_w\mathcal O_{K,w}=\mathcal O_K$，即得 $B_u(N'_u)\subset R^\vee$。源码先证明移位后的估值不等式，再用主分式理想各处指数非负推出整体整性。 [移位的定义](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/QuotientMetricDivisors/DivIntoDualShift.lean#L15-L27) · [`shift_pairing_formula` 与 `divisor_into_dual_shift`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean#L684-L730) · [`divisor_into_dual_lattice`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivIntoDual.lean#L18-L61)

整性之外，还要控制平移和映射的代价。在源码的斜率归一化下，平移使源格均斜率增加 $2\sum_w\mathrm{lw}(w)\tau_w$，其中 $\mathrm{lw}(w)$ 是有限处的对数权重。令 $b=\exp(x^\varepsilon)$。对第 $j$ 个提升，支撑中非基准处的指数预算为
$$
\eta_j=\sum_{\substack{w\in{\rm supp}\\\mu(w)\ne\mu_0}}\mathrm{lwP}(w)e(w)\eta_J(j,w),
\qquad
\eta_j\le D_0 C' x^\varepsilon(B_0+N_c).
$$
这里 $e(w)$ 是分歧指数，$B_0=fmbx^\varepsilon$，$N_c$ 是由秩和 $|T_2|$ 给出的另一项预算。这里 $f$ 是一组节点所用权的个数，$m$ 为提升个数。`LinkN_at` 的原界含按素数加权的上同调长度和 $\sum_\ell\mathrm{vvTerm}(\ell)$，以及 $(\log x)^2N_c$。宿主条件保证各长度有限，并把前一非负和控制在 $\sqrt b$。秩等式给出 $D_0$，充分大的 $x$ 使 $(\log x)^2\le x^\varepsilon$。这就是 `divinN_of_hypV` 供给整除包的预算。 [`ShiftMu`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/QuotientMetricDivisors/DivIntoDualShift.lean#L52-L61) · [`etaSum`、`LinkN_at` 与 `DIVinN_at`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L31-L63) · [两个尺度预算](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalRingCardinality/DataArith.lean#L198-L209) · [`vvRecord` 的有限性与求和](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean#L17-L57) · [`divinN_of_hypV`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean#L79-L130)

列链控制 $B_u$ 在各无穷处的算子范数。对其平方取对数平均，得到非零映射的高度上界 $h(B_u)\le h_u$。行列式比较把局部指数代价和无穷处特征值和写进对偶格余体积，再换成斜率。连同列侧的传递界，它给出
$$
\mu(R^\vee)+h_u-F_o
 \le {\rm MAIN}_L(u)+C|TT|\,a\,{\rm La}
                  +C m(B_0+N_c)x^{C_{\rm abs}\varepsilon}. \tag{D}
$$
$F_o$ 是整除包的基准修正，$\mathrm{MAIN}_L(u)$ 是该字的主项，$TT$ 是一组指定位置，$a$ 与 $\mathrm{La}$ 是尺度因子。`wordFacts_of_clauses` 用格、度量和配对的等式把整性、高度和式 (D) 传到同一份数据。这些等式使下一节框架使用这里的 $N'_u,B_u,R^\vee$。 [`IndefSide.boundsMu`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L271-L334) · [余体积转斜率 `slope_bounds`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/DivisorInequality/DivisorInequalityProofs/BaseLevelBoundsWithCovolumeHolds.lean#L47-L69) · [`divClausesR_of`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean#L184-L247) · [`wordFacts_of_clauses`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean#L179-L225) · [`LinkDIV_at`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L77-L95)

## 4. 用 Bost 型斜率比较消去目标格

设 $W$ 是类 $u_0$ 中的字集，$d_u=\operatorname{rk}N'_u>0$。从每个源格斜率扣去相应的映射高度上界，定义
$$
s_*=\frac{\sum_{u\in W}d_u(\mu(N'_u)-h_u)}{\sum_{u\in W}d_u},
\qquad
U_*=\max_{u\in W}(\mu_{\max}(N'_u)-h_u)-s_* .
$$
$U_*\ge0$ 控制调整后斜率高出均值的幅度。取 $H_H>0$ 且 $H_H\ge s_*-\mu_{\min}(R^\vee)$。Bost 型比较与框架估计给出
$$
s_*-\log|W|-\mathcal E_F \ \le\ \mu(R^\vee),\qquad
\mathcal E_F=\frac{4U_*\log(1+H_H/U_*)+(\eta_F+4\sqrt{e_F})H_H}{1-\delta_F} . \tag{F}
$$
第一项在 $U_*=0$ 时按 $0$ 计。$\eta_F$ 是框架算子的迹平方缺陷参数，$e_F$ 控制各分块的等距缺陷。$0\le\delta_F<1$，目标在复框架的环境空间中至少占 $1-\delta_F$ 的维数。 [`LatGeom` 与 `LatNum`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean#L59-L90) · [分歧压缩与结论](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean#L197-L221) · [`frame_at_of` 的应用](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean#L538-L601)

取阈值 $s_*-\tau$，$\tau>0$。在 $N'_u$ 中保留调整后斜率至少为该阈值的 Harder–Narasimhan 部分。斜率的秩加权均值是 $s_*$，而各项至多 $s_*+U_*$，因此被舍去的秩占比至多 $U_* /(U_*+\tau)$。算术斜率不等式
$$
\mu_{\min}(A)-h(B)\le\mu_{\min}(B(A))
$$
对非零像适用。结合 $h(B_u)\le h_u$ 和映射的整性，保留部分的像落在 $R^\vee$ 的同一斜率阈值以上。源码先在无穷处调整度量，把算子范数的局部界换成平均对数高度，再把该不等式用于每个过滤层。 [平均高度下的斜率不等式](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneqMean.lean#L117-L251) · [秩计数与像落在过滤层](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L194-L306)

要从这些像得到目标格的秩信息，需要一个无穷处的复线性框架。算术映射 $B_u$ 的复化在其中是一个指定坐标块。设包含该坐标块的框架矩阵为 $A_u$，$\gamma_u>0$ 为其权重，$Q_F=\sum_u\gamma_u A_uA_u^*$，$D$ 为环境维数，$t=\operatorname{tr}Q_F$。分块 Hilbert–Schmidt 界和压缩控制给出
$$
\|Q_F-(t/D)I\|_{\mathrm{HS}}^2\le\eta_F\,t^2/D .
$$
若源端丢去秩比例 $\xi$，令 $V_\perp$ 为保留像的张成空间之正交补。各块等距缺陷至多给 $Q_F$ 在 $V_\perp$ 上的迹贡献 $R_{\rm src}(\xi+\sqrt{\xi e_F})$，其中 $R_{\rm src}=\sum_u d_u$。另一方面，全迹 $t\ge R_{\rm src}(1-\sqrt{e_F})$，而中心化的迹界给出在任意 $w$ 维子空间上的迹下界 $(t/D)w-\sqrt w\,\|Q_F-(t/D)I\|_{\mathrm{HS}}$。联立得 $\dim V_\perp\le D(\eta_F+4\xi+4\sqrt{e_F})$。 [分块界 `InputSG`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean#L27-L35) · [实际框架与整除数据的连接](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/LinkMin.lean#L711-L721) · [`frame_linear_algebra_first`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/FrameLinearAlgebraFirst.lean#L77-L221)

投到目标块后，至少保留 $\operatorname{rk}R^\vee-\dim V_\perp$ 个独立方向。于是目标中斜率低于 $s_*-\tau$ 的比例至多
$$
\frac{\eta_F+4U_* /(U_*+\tau)+4\sqrt{e_F}}{1-\delta_F}.
$$
每个斜率 $\lambda_j$ 对均值的负向贡献至多为 $(s_*-\lambda_j)_+$。把低斜率比例从 $0$ 积到 $H_H$，就控制了这些正部的平均值。这里用的是 $\mathcal E_F$ 的积分式，源码另行处理 $U_*=0$，并在实际用到的版本中以 $\log |W|$ 放宽结论。装配时统一的缺陷参数满足 $(\bar\eta_F+4\sqrt{\bar e_F})x^{C_H}\le6$，配合 $H_H\le x^{C_H} b$ 的记录界，框架缺陷项进入后续误差预算。 [`theoremFSharp_of` 的目标秩和积分](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L277-L386) · [`frame_theorem_log_ideal`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L388-L400) · [统一缺陷预算](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean#L629-L646) · [误差预算中的使用](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean#L219-L247)

整除侧以另一种方式使用 $s_*$。把式 (D) 与商格斜率界、各字的整除指数和计数比较合用，`s_lower5` 得到
$$
G_a(u_0)+\mu(R^\vee)-K_5(u_0)-\langle{\rm Lo}_5\rangle_d\le s_* .
$$
$G_a$ 是计数中的增益，$\langle{\rm Lo}_5\rangle_d$ 是按 $d_u$ 加权的商格误差。把这个下界代入式 (F) 就消去 $\mu(R^\vee)$。恒等式 `key_identity5` 把 $K_5(u_0)$ 写成 $\mathrm{Main}(u_0)+K_0$，于是
$$
G_a(u_0)-{\rm Main}(u_0)
   \le K_0+\langle{\rm Lo}_5\rangle_d+\log|W|+\mathcal E_F.
$$
再计入实际计数 $\mathrm{ASK}$ 与增益 $G_a$ 的损失，得到逐类的 $\mathrm{ASK}(u_0)-\mathrm{Main}(u_0)\le\mathrm{ErrX5at}(u_0)$。 [`s_lower5` 与 $K_5,K_0$](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L21-L66) · [`key_identity5` 与 `Ga_bound5`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L105-L160) · [`each_unit_bound_statement`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L175-L197)

## 5. 从计数上界到平方根窗口

逐类的计数误差可用有限 Fourier 恒等式写成 $L$ 函数误差。宿主数据的群为 $E_0\times H$，其中 $E_0=(\mathbb Z/2)^2$，$H$ 是有限阿贝尔群。记 $\Phi_0$ 为第一坐标为零的子群。对素数幂 $p^j$，字符系数是在 $j\,{\rm Frob}_p+I_p$ 上对加法特征取平均，$I_p$ 为惯性群。对节点参数 $a>0$、正权 $w$ 和满足 $N\ge a/w(g)$（$g\in\Phi_0$）的截断，`ch_balance` 给出
$$
{\rm ASK}-{\rm MAIN}
  = \frac1{|\Phi_0|}\sum_{g\notin\Phi_0}\sum_{\xi}
       \overline{\xi(g)}\, w(t,g)\,
       G_\xi^{\rm ar}\!\left(\frac{a}{w(t,g)}\right).
$$
这里 $\xi$ 遍历该有限群的对偶，$w(t,g)$ 是经配对置换读出的权，$G_\xi^{\rm ar}$ 用上述惯性平均作系数。正交性只留下 $\Phi_0$ 外的 Frobenius 与惯性陪集项。宿主假设使坏素数集合中的惯性和 Frobenius 都落在 $\Phi_0$。通常的非分歧惰性项带 $2\log p$，特别的素数 $d$ 的二阶惯性群跨过两个陪集，给出 $\log d$ 的项。平滑和的修正项给出左边的主项。`IdentU` 和 `ch_top` 逐项核对这个主项与上一节用到的主项，并把各节点的实部之和识别为同一个 $\mathrm{ASK}(u_0)-\mathrm{Main}(u_0)$。 [宿主的分歧条件 `HostFactsS`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean#L14-L22) · [惯性平均、计数与主项的定义](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean#L61-L96) · [`ch_balance`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean#L200-L260) · [`ch_top` 中的识别](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L11-L54)

令 $n=|H|$，$n_T=|TT|$，$n_2=|T_2|$，其中 $TT,T_2$ 是宿主的两个选定子集。用 $a_E\le2xb$ 表示计数记录中的规模参数。整除及损失的指数预算用 $e_D,e_L$ 控制时，`ch_top` 与 `core_gm` 给出的逐类误差至多 $x^{C_*\varepsilon}B_{\rm err}$，其中 $C_*=e_D+e_L+3$，且
$$
B_{\rm err}= n_Ta_E(1+m^2/k)
      +m\left(2nm b\,x^\varepsilon+
                       \frac{n_2 k b\,x^\varepsilon}{n^2x^{-\varepsilon}}\right).
$$
常数和对数因子已计入 $3\varepsilon$。这一步把斜率消去后的误差写成可直接与有限和的归一化因子比较的量。 [`errX5at_le`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L613-L672) · [`ch_top` 的误差比较](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L37-L72) · [`core_gm` 中的指数预算](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L46-L60)

在厚节点上，$b\le w\le b+\eta+1$，用 Lipschitz 界把 $w$ 换成 $b$，并用参数条件 $|a_t/b-x|\le1$ 比较平滑和的自变量。薄节点满足 $0<w\le2b'$，由 $x\ge3$ 和 $b'X'\le xb$ 得 $a_t/w\ge X'/3$，因而可用 $|G_\xi^{\rm ar}(y)|\le\theta_{\rm thin}y$ 的薄区间界。取 $f=|\Phi_0|$，源码用 $2f(x+1)\theta_{\rm thin}\le 1/x$ 和 $6f(x+1)(\eta+1)\le b/x$ 将两类节点的代价控制在每节点 $2b/x$。随后对包含 $T_2$ 的子群 $H_0\subset H$ 做平均，正交性保留在 $H_0$ 上平凡的特征。设 $G_{m,A}$ 是其中指定保留特征的加权和，$\Sigma_A$ 是其余特征的绝对误差和。集合 $TT$ 上的特征和误差控制给出
$$
Q\frac{\delta_2}{2}
 \left(G_{m,A}(x)-\Sigma_A(x)-4x^{1/2+\varepsilon}\right)
 \le x^{C_*\varepsilon} B_{\rm err} +\frac{2Q}{x},
\quad Q=n_Tmb,\quad \delta_2=\frac{n_2}{n}. \tag{A}
$$
这里 $Q$ 来自 $n_Tm$ 个节点及厚权 $b$，$\delta_2/2$ 来自子群平均中厚位置的贡献。 [厚薄比较 `th_le`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L75-L152) · [厚权和薄区间条件](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean#L42-L62) · [两类节点的代价条件](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/SChain.lean#L50-L58) · [子群平均](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L283-L338) · [`ch_core` 的特征移动](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L419-L442)

平方根来自秩的选择。对 $0<\varepsilon<1/52$，先在给定大小的框架上取偶数 $m$，使它介于 $\sqrt{x\,x^{-\varepsilon/8}}$ 和它的两倍之间，再把偶数 $k$ 取在 $x^{9/2+10\varepsilon}$ 与其两倍之间。实现后的数值条件给出
$$
x^{1/2-\varepsilon}\le m\le x^{1/2+\varepsilon/2},
\quad xm\le k\le n^2 x^{1/2-\varepsilon},
\quad n_T\ge \tfrac12 n x^{-\varepsilon/8},
\quad \delta_2\ge x^{-\varepsilon}.
$$
于是 $B_{\rm err}/Q$ 的四项分别受 $2x/m,\ 2xm/k,\ 2nm x^\varepsilon/n_T,\ (n_2/n_T)(k/n^2)x^{2\varepsilon}$ 控制。其中 $x/m\le x^{1/2+\varepsilon}$，$xm/k\le1$，第三项至多 $4x^{1/2+13\varepsilon/8}$，第四项至多 $2x^{1/2+9\varepsilon/8}$。所以 $B_{\rm err}/Q\le10x^{1/2+13\varepsilon/8}$。式 (A) 再除去密度因子，损失 $x^\varepsilon$。再用充分大时的 $26\le x^{3\varepsilon/8}$ 吸收常数，得到 $G_{m,A}\le\Sigma_A+x^{1/2+(C_*+3)\varepsilon}$。宿主的特征对应给出 $G_{m,A}=G_{\mathcal L}$，并给出 $\Sigma_A\le 4o\,x^{1/2+\varepsilon}$。固定等级后将 $1+4o$ 吸收进 $x^\varepsilon$，得到指数 $1/2+(e_D+e_L+7)\varepsilon$。 [`exists_ranks_rankVal_frame`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsRanksRankValFrame.lean#L45-L100) · [秩和集合大小传入窗口](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/RamificationTwoAndConjugationAtQAndD.lean#L632-L670) · [`proposition_size_bound`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L507-L592) · [`gmA_eq`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean#L61-L80) · [`sigA_le`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean#L38-L60) · [`core_gm` 的吸收](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L55-L74)

逐尺度估计要用于 (W)，同一数据族必须同时承载宿主条件、整除和斜率输入。`topDesWin` 将这些最终成立的条件合并后再选族，得到在该族的大尺度上成立的 `ChainTied`。`tiedCore_of_chainTied` 从中取出所选宿主上的点态条件 `CoreAtH`，保留集合 $TT$ 的识别等式。`windowInequality_of_artinInputs` 取宿主、族与数值估计三个阈值的最大值。`zeroFreeAll_of_topG` 按每个 $\psi$ 将这些条件与 `HasWindows` 合用。这样才能让整个 $[Y,Y^{3/2}]$ 落到逐点估计的适用范围内。 [同一家族的选择 `topDesWin`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean#L11-L31) · [点态输入 `tiedCore_of_chainTied`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean#L13-L30) · [统一阈值](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean#L11-L25) · [逐本原特征的窗口装配](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean#L16-L34)

## 6. 单侧 Landau 怎样排除零点

设 $\rho_0$ 是保留特征的一个假定零点，$\beta=\Re\rho_0>1/2$。先选 $\theta=\tfrac12+\tfrac12\min(\beta-\tfrac12,\tfrac12)$，再选足够小的 $\varepsilon>0$，使 $9\varepsilon\le\theta-\tfrac12$。这样 $0<\theta<1$，并有 $\theta<\beta$。由 (W) 得到任意靠后的窗口 $[Y,Y^{1+\delta}]$ 上 $G_{\mathcal L}(y)\le y^\theta$，其中 $\delta=1/2$。置 $g(u)=G_{\mathcal L}(e^u)$ 和 $U=\log Y$。在 $[U,(1+\delta)U]$ 上，$g$ 有非负包络 $R(u)=e^{\theta u}$，且
$$
\int_U^{(1+\delta)U}R(u)e^{-\theta u}\,du=\delta U\le e^{\lambda U}
$$
对任意固定 $\lambda>0$ 及充分大的这些 $U$ 成立。这正是 Landau 所需的窗口量词。 [`level_of_tiedWin` 的参数顺序](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L59-L81) · [等级上的 `formB`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean#L8-L19) · [幂包络与对数换元](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/WindowHypOfRpow.lean#L27-L57) · [`windowHypU_of_windowHyp`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/WindowHypUOfWindowHyp.lean#L29-L56)

### 零点给出不会抵消的极点

在 $\Re z>2$ 时令 $\mathcal P(z)=\int_0^\infty g(u)e^{-zu}\,du$。换回 $y=e^u$ 后，平滑核的 Mellin 积分为 $\int_n^\infty (y/n-1)y^{-z-1}\,dy=n^{-z}/[z(z-1)]$。因此求和引入 $-L'(\chi,z)/L(\chi,z)$，而第 1 节的修正项给出分子里的其余部分。对单个特征，源码把变换写成
$$
-\frac{f'(z)/f(z)-z f'(1)/f(1)+\kappa(1-z)}{z(z-1)} .
$$
非平凡情形取 $f=L(\chi,\cdot)$、$\kappa=0$。模一情形用 $(z-1)\zeta(z)$ 的整函数延拓，取 $f(1)=1$、$\kappa=1$。分子在 $1$ 为零，源码以差商处理这一点。取平滑和的实部，相当于把 $\chi$ 与 $\chi^{-1}$ 的变换对称平均，再以 $a_\chi$ 加权。因而对右半平面的零点及其共轭，族变换在 $\rho$ 的留数为
$$
-\frac{S(\rho)}{\rho(\rho-1)},\qquad
S(\rho)=\sum_\chi \frac{a_\chi}{2}
  \left(\operatorname{ord}_\rho L(\chi,\cdot)
       +\operatorname{ord}_\rho L(\chi^{-1},\cdot)\right)>0 .
$$
每个零点重数非负，且至少一项为正。共同的因子 $-1/[\rho(\rho-1)]$ 因而无法在求和时被抵消。若极点在实轴上，则 $0<\rho<1$，留数为正实数。这里的边界使用源码调用的 $\Re s\ge1$ 非消失结果。`PoleData` 同时给出 $g$ 的可测性、全局粗界 $|g(u)|\le C_0e^{2u}$ 和极点的离散性。 [平滑核的 Mellin 积分](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/MellinRamp.lean#L10-L52) · [Mellin 变换与对数导数](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean#L116-L145) · [单特征变换及主部](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L22-L89) · [模一与非平凡特征的计算](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L137-L239) · [族变换及留数](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean#L248-L400) · [`PoleData` 的条件](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L9-L29) · [`lemmaL`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean#L13-L22)

### 单侧信息控制两个 Taylor 系数的组合

取充分大的固定 $\sigma>2$，定义 $A_k(z)=(-1)^k\mathcal P^{(k)}(z)/k!$。在 $z=\sigma+i\gamma'$，这个量是 $g(u)$ 对非负权 $u^k e^{-\sigma u}/k!$ 和相位 $e^{-i\gamma'u}$ 的积分。取其模并加上实中心的 $\Re A_k(\sigma)$ 后，上界的被积函数含有
$$
|g(u)|+g(u)=2\max(g(u),0).
$$
在好窗口内，它由 $2R(u)$ 控制。由指数级数有 $u^k e^{-(\sigma-\theta)u}/k!\le(\sigma-\theta)^{-k}$，因此窗口积分带因子 $(\sigma-\theta)^{-k}$。窗口外则用全局粗界和尾积分估计。尾估计选 $k=\lceil(1+\delta/2)\sigma U\rceil$，使权集中在窗口内，并把窗口外的 $\int u^k e^{(2-\sigma)u}\,du/k!$ 控制在 $C/\sigma^k$。由此，对任意 $\lambda>0$ 都有任意大的 $U$ 和一个共同的 $k\ge U$，使
$$
|A_k(\sigma+i\gamma')|+\Re A_k(\sigma)
   \le C_1 e^{\lambda U}(\sigma-\theta)^{-k} \tag{L}
$$
同时对所有 $\gamma'\in\mathbb R$ 成立。这是算术单侧上界在解析部分发挥作用的地方。 [`landau_coeff`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauCoeff.lean#L10-L28) · [`landau_window_ineq`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindowIneq.lean#L57-L109) · [`landau_tails`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauTails.lean#L80-L131) · [`landau_window_key`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L40-L73)

### 极点给出更快的系数增长

若 $\Re\rho>\theta$ 的极点存在，`landau_dichotomy` 给出两种情形。第一种有一个以 $\sigma$ 为中心、半径 $D\le\sigma-\theta$ 的无极点开圆盘，同时有极点到直线 $\Re z=\sigma$ 的水平距离小于 $D$。沿该直线稍移中心，避开使最近极点并列的有限个虚部，得到一个只含一个最近极点的圆盘。设该极点距新中心 $d<D$。减去主部后，Cauchy 界以较大半径 $r>d$ 控制误差，故 $\lvert A_k(\sigma+i\gamma')\rvert\ge |c|d^{-k-1}-M r^{-k}$。实中心无极点，$\Re A_k(\sigma)$ 的负部也由同阶的 Cauchy 界控制。第二种在实中心的某个圆盘内只有一个实极点，距离为 $d$。正留数使 $\Re A_k(\sigma)$ 本身有正主项 $c d^{-k-1}$，再加一个模仍给出下界。 [`landau_dichotomy`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauDichotomy.lean#L24-L87) · [移动中心 `landau_nearest`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauNearest.lean#L36-L109) · [`landau_pole_asym`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauPoleAsym.lean#L19-L79) · [两种情形的合成 `landau_window`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L166)

两种情形都得到某些固定 $c_0>0$ 与 $0<d<r\le\sigma-\theta$，使 (L) 蕴含
$$
c_0 d^{-k}\le M r^{-k}+C_1e^{\lambda U}(\sigma-\theta)^{-k}.
$$
先选 $0<\lambda<\log(r/d)$，再取任意大的相应窗口。乘以 $d^k$ 后，右边由常数乘 $(d/r)^k$ 和 $\exp\big((\lambda-\log(r/d))U\big)$ 控制，趋向零，因为 $k\ge U$。这与 $c_0>0$ 矛盾。原假定零点会产生 $\Re\rho_0>\theta$ 的极点，所以被排除。最后选的 $\lambda$ 只决定窗口要有多晚，这已经由包络积分的量词保证。 [`landau_window_contra`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L20-L38) · [幂窗口推出无零点 `zeroFree_of_rpow_window`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean#L11-L14)

## 7. 回到源码声明

本原特征在 $\Re s>1/2$ 的非消失接下来用于处理所有特征。`imprimitive` 通过导子特征扩展到一般特征。在 $\Re s>0$，补上的有限 Euler 因子 $1-\chi_{\rm prim}(p)p^{-s}$ 都非零，因为 $\lvert\chi_{\rm prim}(p)p^{-s}\rvert<1$。主特征在 $s=1$ 的例外单独处理。在 $0<\Re s<1$，本原函数方程把左半带的零点送到逆特征在 $1-s$ 的零点，所用 Gamma 因子非零。模一情形给出 zeta 的右侧非消失，再由 zeta 函数方程处理左侧及平凡零点条件。 [`imprimitive`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean#L5-L35) · [`prim_reflect` 与 `strip`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L23-L73) · [`critLine` 与 `rh_of_every`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/GammaFactorNonvanishing/CritLine.lean#L6-L32) · [zeta 的左侧处理](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean#L5-L62)

`Main.lean` 经 `MainTheoremsAll`、`MainTheoremsCritical` 导入 `MainTheorems`。其中 `allChi` 指向 `UpperTheory.FinalTheorems.everyCharacter`。五个导出分别是 Mathlib 的 RH 命题、zeta 零点的临界线陈述、Dirichlet $L$ 函数的右侧非消失，以及一般和本原特征的带内临界线陈述。它们共享上面的右侧结果。 [`MainTheoremsAll`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Supplements/Kernels/MainTheoremsAll.lean#L1-L2) · [`MainTheoremsCritical`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Supplements/Kernels/MainTheoremsCritical.lean#L1-L4) · [`allChi` 与各包装](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Supplements/Kernels/MainTheorems.lean#L7-L16) · [`Main.lean` 的五项导出](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Main.lean#L1-L12)

## 关键输入与接缝

| 接缝 | 主链用到的输入与得到的结论 |
| --- | --- |
| Theta 到行列数据 | 读取了匹配命题、扭曲积分比较、行测试及求值网格的装配。Eisenstein 与 Siegel–Weil、非零倍增积分、各处重数一、系数域和余体积的底层构造在这里按其声明使用。 [`theoremK_head2`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean#L14-L27) · [接收 theta、余体积和局部行界的装配](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L44-L73) |
| 行列数据到算术格 | 在已提供 `adm2`、局部列识别与格相容条件下，移位、逐处取整及整体对偶格包含关系可以沿证明体逐步推出。局部整除的原始估计、行列式除子预算和商格估计各有进一步输入。 [局部估值接口](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/LocalToGlobal/GroupLattices/ServJointF.lean#L84-L102) · [移位整性](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean#L684-L730) · [余体积使用的除子界](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/DivisorInequality/DivisorInequalityProofs/BaseLevelBoundsWithCovolumeHolds.lean#L52-L69) |
| 同一目标格到窗口 | 已给整格映射、高度、框架分块和斜率预算后，过滤层秩估计与斜率消去给出计数界。Fourier 归一化需要厚薄尺度、特征和与秩大小条件。窗口还需要 `VWin`、宿主构造及相容族的供应，尤其是这些条件如何落到同一家族。 [`linkGLOBAL7_items` 的合用](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Formalism/SharpRestriction/GlobalSchurBounds/LinkMin.lean#L711-L721) · [宿主构造接口](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean#L17-L23) · [`topDesWin` 取同一家族](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean#L11-L31) |
| 窗口到零点 | 给定 (W)，正权留数、单侧矩估计和 Cauchy 比较构成解析推导。这里用到的标准非消失和函数方程保留为源码调用。 [`lemmaL`](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean#L13-L22) · [窗口极点论证](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L166) · [反射调用](https://github.com/leanprover-community/riemann-hypothesis/blob/371a1a26d5e17f604428e3a8ce6ce341cf517434/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L35-L57) |

复核范围是上述源码正文与接缝。第一轮路线图另记了阅读范围和待查依赖。本次补读了平移整性及局部化推出整体整性的证明体。Lean、Lake 和第三方代码均未执行，传递依赖的完整性与内核验收仍待独立核对。
