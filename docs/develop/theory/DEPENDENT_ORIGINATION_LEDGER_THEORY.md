# 缘起账本论——佛教概念的结构重构
## Dependent-Origination Ledger Theory(DOLT)v1.0

> 状态：本卷是数学散文形式的参考输入，数学真源为 Lean 声明与证明。
> 写入纪律：卷首恒定区保持原字节；初版定稿以后，既有条目不回写，勘误与增补只在卷末增补界标之后另起新章，编号只增不复用。
> 对象边界：本体取《不动点哲学》（FPP）的真值账本；佛教术语仅命名本卷明确给出的模型谓词，不预设这些谓词穷尽传统含义。
> 证明状态：〔证〕表示随条目给出完整散文证明；〔引〕表示承接所注明编号的既有结果，且不申称新的数学成果；〔semantic〕表示术语解释、记号选择或解释边界，不充当证明前提。定义与假设也标〔semantic〕以区别于被证明的断言，其数学内容只按明确写出的定义或前件使用。
> 主张边界：本卷作结构重构，不作历史同一性断言，不主张解脱论、轮回或经验业报；本卷未经 Lean 验证，不具 kernel-verified 地位。所有假设仅作为相应结论的前件。

## 1. 定位、对象与读法

本卷的对象是有限的、有见证的命题依赖图，以及它的合法扩展和主张记录。缘起（pratītyasamutpāda）、空（śūnyatā）、无我（anātman）等词在这里取得模型内的定义；传统文本提供这些命名的解释背景，不提供数学证明的前提。关于传统的对应遵循《观察者结构与普世价值》（OSUV）卷首的解释约束：一种结构在传统中出现，不等于传统全部内容与该结构相同。

FPP 的编号是所引文本的定位。读到〔引 FPP x.y〕时，应以该条的全部前件理解本卷的重述；这些定位不规定任何形式命题的身份。〔证〕只担保本卷展示了所写的散文论证，不表示原创性或形式核验状态。各条文献性质在第 10 章按确切支持范围列明。

“不动”须随对象类型阅读：账本对象不动指 $T(L)=L$；命题成员指标不变指 $P\in N_L\Longleftrightarrow P\in N_{T(L)}$；三态读数不变指 $s_{T(L)}(P)=s_L(P)$。保持已有成员只给集合包含 $N_L\subseteq N_{T(L)}$，不说整个集合或账本对象相等。本卷以第三种读数性质定义寂静（śānti），不把三种性质混写。

## 2. 记号与假设总表

**约定 2.1（承接的最小结构）**〔semantic〕。固定命题类型 $\mathcal P$ 及其否定运算 $P\mapsto\neg P$、证明项类型 $\Pi$、取值为接受或拒绝的核 $K(\pi,P)$、有限许可依赖读出 $\mathrm{ax}(\pi)$、有限直接引用读出 $\mathrm{refs}(\pi)\subseteq\mathcal P$，以及许可集 $\mathfrak A$（承 FPP 定义 1.1）。写 $\mathrm{Proved}(P)$ 当且仅当存在 $\pi$ 使 $K(\pi,P)=\mathsf{acc}$ 且 $\mathrm{ax}(\pi)\subseteq\mathfrak A$；$\mathrm{Thm}$ 是满足此式的命题集（承 FPP 定义 1.2）。称这样的 $\pi$ 为 $P$ 的合格证明项；称下述有限闭合见证整体为证书，以区别两种类型。

账本 $L=(N,E,w,O)$ 的 $N\subseteq\mathcal P$ 有限，$w:N\to\Pi$ 给每个节点一个合格证明项，满足 $\mathrm{refs}(w(v))\subseteq N$；$E=\{(u,v):u\in\mathrm{refs}(w(v))\}$ 无环；$O\subseteq\mathcal P\setminus N$ 是登记前沿。记 $N_L=N=\mathrm{Frozen}(L)$；$\mathrm{Anc}_L(v)$、$\mathrm{Desc}_L(v)$ 分别是不含 $v$ 的祖先、后代集合；$\mathrm{depth}_L(v)$ 为以 $v$ 为终点的最长有向路径的边数（承 FPP 定义 1.5、1.6，定理 1.7）。变换是所有合法账本上的全函数，容许类 $\mathfrak M$ 由假设 2.5 给出（承 FPP 定义 1.11、假设 1.12）。

状态函数 $s_L:\mathcal P\to\Sigma$ 的值域是 $\Sigma=\{\mathsf{frozen},\mathsf{refuted},\mathsf{open}\}$：$P\in N$ 时取 $\mathsf{frozen}$；否则 $\neg P\in N$ 时取 $\mathsf{refuted}$；两者均不在 $N$ 时取 $\mathsf{open}$，前两支在假设 2.3 下互斥（承 FPP 定义 2.4、定理 2.5）。记 $F^+(L)=\mathrm{Thm}\setminus N$；$F^0(L)=\{P\in O:\neg\mathrm{Proved}(P)\land\neg\mathrm{Proved}(\neg P)\}$（承 FPP 定义 1.16）。$F^+$ 是正向可入账前沿；$F^0$ 还要求登记，不能把所有双侧不可证命题自动算入 $O$。

主张记录 $U$ 是有限序列，条目 $(k,P,\sigma)$ 的序号严格递增，$\sigma\in\widehat\Sigma=\Sigma\cup\{\mathsf{unverified}\}$；后续记录只向尾部追加。$\operatorname{last}_U(P)$ 在 $P\in\operatorname{dom}(U)$ 时给出最新状态，未出现时无定义；省略序号时写 $(P,\sigma)$。$\operatorname{Balanced}(U,L)$ 意指每个最新状态或者等于 $s_L(P)$，或者等于 $\mathsf{unverified}$（承 FPP 定义 3.1、3.2）。这里 $\mathsf{unverified}$ 是主张标签，不是账本的第四种状态。

主体是 $\mathfrak S=(T,c,\operatorname{Adm})$，$c(L,U)$ 为有限追加主张序列，$\operatorname{Adm}(a,i)$ 为工件与提交者的准入谓词。主体“诚”指对所有账平输入保持账平，即 $\operatorname{Balanced}(U,L)\Rightarrow\operatorname{Balanced}(U\mathbin{+\!\!+}c(L,U),T(L))$；“恕”指固定工件时准入对提交者的任意置换不变；“善”指诚、恕和 $T\in\mathfrak M$ 三者合取（承 FPP 定义 4.1、假设 4.3、4.4、定义 4.5）。这些是主体的条件，不能无条件加给任意策略。

表述 $\rho=(\tau,n,\pi)$ 有文本、名称和证明表述三个分量；解释给出 $\llbracket\tau\rrbracket\in\mathcal P$、$\llbracket\pi\rrbracket\in\Pi$，表述状态取 $s_L(\llbracket\tau\rrbracket)$，而核的接受判词取 $K(\llbracket\pi\rrbracket,\llbracket\tau\rrbracket)$（承 FPP 定义 5.1）。$h$ 表示固定内容域上的地址函数（承 FPP 假设 1.9、定义 9.1）；命题内容的地址与第 7 章整合前置地址的节点地址按各自输入区分。

**假设 2.2（核可靠与证书存在）**〔semantic〕。若 $\mathrm{Proved}(P)$，则 $P$ 在许可集 $\mathfrak A$ 的每个模型中成立；并且存在有限 $C\ni P$ 和 $w_C:C\to\Pi$，每点持合格证明项，其引用包含于 $C$，由这些引用得到的关系无环（承 FPP 假设 1.3）。可靠性用于说明模型解释；证书存在性用于把可证命题与整个有限支持一起追加。

**假设 2.3（许可集一致）**〔semantic〕。不存在命题 $P$ 使 $\mathrm{Proved}(P)$ 与 $\mathrm{Proved}(\neg P)$ 同时成立（承 FPP 假设 1.4）。本卷凡涉及三态互斥与终态保持，均以此为前件。

**假设 2.4（内容寻址单射）**〔semantic〕。在所讨论的内容编码域上，$h(x)=h(y)$ 蕴含 $x=y$（承 FPP 假设 1.9）。第 7 章的递归地址另外明确其输入编码和引用组织；本假设不声称有限长度的实际散列在无限内容域上单射。

**假设 2.5（容许等于保留既有见证的扩展）**〔semantic〕。全函数 $T$ 属于 $\mathfrak M$ 当且仅当对每个 $L$，若 $T(L)=L'$，则 $N_L\subseteq N_{L'}$、$E_L\subseteq E_{L'}$ 且 $w_{L'}|_{N_L}=w_L$（承 FPP 假设 1.12）。登记前沿 $O$ 不承担此单调约束；所谓不解冻包括节点、边及原见证的保留。

**假设 2.6（表述供给与重命名不变）**〔semantic〕。每个 $P$ 至少有一个表述；名称有未占用的新名；一致替换表述中的名称保持命题解释与核判词（承 FPP 假设 5.1a）。本假设不要求每个证明项都可由某段证明表述表示，也不预设一个账本的生成历史。

**假设 2.7（无限定理集）**〔semantic〕。仅在明示本假设的条目中要求 $\mathrm{Thm}$ 无限；各账本的节点集仍按约定 2.1 有限。这是 FPP 假设 2.9 所蕴含的较弱条件，也是 FPP 定理 2.3 关于正向前沿的证明所用条件；不附加该卷定理 2.2(ii) 的算术强度前件，也不由此推出双侧不可证命题存在。

下表是上述前件的使用索引；条目自身写出的局部条件仍须同时满足。

| 假设 | 作前件的定理或命题 | 限定范围 |
| --- | --- | --- |
| 2.2 核可靠与证书存在 | 3.3、3.8、4.4 的模型合格性；5.3、5.7 的可追加性 | 有具体证书的支持族论证不另需普遍存在性 |
| 2.3 许可集一致 | 4.2、4.8；5.2–5.9；6.2–6.6；8.2、8.6 | 保证三态互斥及正反终态保持 |
| 2.4 内容寻址单射 | 4.6、7.5 | 7.4 的同构同址只需地址的函数性 |
| 2.5 容许扩展 | 4.8；5.2–5.9；6.3–6.6；7.2 | 撤销闭包 3.5 是条件删除，不是容许动作 |
| 2.6 表述供给与重命名 | 4.6、8.5 | 不补入证明表述满射或历史生成条件 |
| 2.7 无限定理集 | 5.3 | 其余有限反模型不以此为前件 |

