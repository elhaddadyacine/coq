(* Formalization of Arithmetic as presented in "Proofs in  theories : Chapter 4" by Gilles DOWEK *)
Section Arithmetic.

(* iota sort to represent elements *) 
Parameter (iota: Set).
(* kappa sort to present sets *)
Parameter (kappa: Set).
(* Constant 0 *)
Parameter O : iota.
(* Function symbol expressing successor *)
Parameter S : iota -> iota.
(* Function symbol expressing predecessor *)
Parameter Pred : iota -> iota.
(* Function + *)
Parameter Plus : iota -> iota -> iota.
(* Function x *)
Parameter Mult : iota -> iota -> iota.
(* Null predicate *)
Parameter Null : iota -> Prop.
(* Equality predicate *)
Parameter Eq : iota -> iota -> Prop.
(* In predicate to express that an element belongs to a set *)
Parameter In : iota -> kappa -> Prop.
(* The comprehension scheme *)
Axiom ax_compr: forall A, exists c, forall y, In y c <-> A y.
(* The equality axiom *)
Axiom ax_equality: forall x y, Eq x y <-> forall c, (In x c -> In y c).
(* The induction axiom *)
Axiom ax_induction: forall c, In O c -> (forall x, (In x c -> In (S x) c)) -> forall y, In y c.

(* Pred O = O *)
Axiom ax_pred_O: Eq (Pred O) O.
(* Pred (S x) = x *)
Axiom ax_pred_S: forall x, Eq (Pred (S x)) x.
(* O + y = y *)
Axiom ax_plus_O: forall y, Eq (Plus O y) y.
(* (S x) + y = S (x + y) *)
Axiom ax_plus_S: forall x y, Eq (Plus (S x) y) (S (Plus x y)).
(* O * y = O *)
Axiom ax_mult_O: forall y, Eq (Mult O y) O.
(* (S x) * y = (x * y) + y *)
Axiom ax_mult_S: forall x y, Eq (Mult (S x) y) (Plus (Mult x y) y).
(* Null (0) *)
Axiom ax_null_O: Null O.
(* ~ Null(S x) *)
Axiom ax_neg_null_S: forall x, not (Null (S x)).

(* Comprehension scheme for one element *)
Lemma compr1: forall A, forall x : iota, exists c, forall y : iota, In y c <-> A x y.
Proof.
intros A x.
apply (ax_compr (A x)).
Qed.

(* Comprehension shceme for two elements *)
Lemma compr2: forall A, forall x1 x2 : iota, exists c, forall y, In y c <-> A x1 x2 y.
Proof.
intros A x1 x2.
apply (ax_compr (A x1 x2)).
Qed.

(* Reflexivity : x = x *)
Lemma eq_refl: forall x, Eq x x.
Proof.
intros x.
apply (ax_equality x x).
intros C Hxc.
apply Hxc.
Qed.

(* Transitivity : if x = y and y = z then x = z *)
Lemma eq_trans: forall x y z, Eq x y -> Eq y z -> Eq x z.
Proof.
intros x y z Hxy Hyz.
apply (ax_equality x z).
intros C Hxc.
apply (ax_equality y z).
apply Hyz.
apply (ax_equality x y).
apply Hxy.
apply Hxc.
Qed.

(* Symmetry : if x = y then y = x *)
Lemma eq_sym : forall x y, Eq x y -> Eq y x.
Proof.
intros x y Hxy.
pose proof (ax_compr (fun z => Eq z x)) as [C Hcx].
apply Hcx.
apply (ax_equality x y).
apply Hxy.
apply Hcx.
apply eq_refl.
Qed.

(* Proposition 1 in Exervice 4.1: if S x = S y then x = y *)
Theorem s_inj: forall x y, Eq (S x) (S y) -> Eq x y.
Proof.
intros x y Heqs.
pose proof (ax_equality (S x) (S y)) as [Heqii Hiieq].
pose proof (ax_compr (fun z => Eq (Pred (S x)) (Pred z))) as [D Hieq].
pose proof (Hieq (S x)) as [Hisx Heqsx].
pose proof (Heqsx (eq_refl (Pred (S x)))) as Hixd.
pose proof (Heqii Heqs) as Hii.
pose proof (Hii D Hixd) as Hiyd.
pose proof (Hieq (S y)) as [Hsyd Heqsxy].
pose proof (Hsyd Hiyd) as Hsxsy.
apply (eq_trans x (Pred (S x)) y).
apply eq_sym.
apply ax_pred_S.
apply (eq_trans (Pred (S x)) (Pred (S y)) y).
apply Hsxsy.
apply ax_pred_S.
Qed.

(* Propositoin 2 in Exercice 4.1: O =/= S x *)
Theorem neg_s_eq_O: forall x, ~ (Eq O (S x)).
Proof.
intro x.
intro HOsx.
pose proof (ax_null_O) as HnullO.
pose proof (ax_neg_null_S) as HnullS.
pose proof (ax_equality O (S x)) as [Heqsx Hinsx].
pose proof (Heqsx HOsx) as HiOiS.
pose proof (ax_compr (fun z => Null z)) as [D Hnullz].
pose proof (HiOiS D).
pose proof (Hnullz (S x)).
pose proof (Hnullz O) as [HiOnull HnulliO].
pose proof (H (HnulliO HnullO)).
destruct (Hnullz (S x)).
pose proof (H2 H1).
apply (HnullS x).
apply H4.
Qed. 


(* Lemma used to proof Exercice 4.2  (x = y -> S x = S y) *)
Lemma s_eq : forall x y, Eq x y -> Eq (S x) (S y).
Proof.
intros x y Hxy.
apply (ax_equality (S x) (S y)).
intro C.
pose proof (ax_compr (fun z => In (S z) C)) as [D Hiysy].
intro Hsx.
apply Hiysy.
apply (ax_equality x y).
apply Hxy.
apply Hiysy.
apply Hsx.
Qed.

(* Proposition of Exervice 4.2 : x + 0 = x *)
Theorem plus_x_left: forall x, Eq (Plus x O) x.
Proof.
intro x.
pose proof (ax_compr (fun x => Eq (Plus x O) x)) as [C Hieq].
apply Hieq.
apply ax_induction.
apply Hieq.
apply ax_plus_O.
intros n Hinsn.
apply (Hieq (S n)).
pose proof (Hieq n) as [Hineq Heqin].
apply (eq_trans (Plus (S n) O) (S (Plus n O)) (S n)).
apply ax_plus_S.
apply s_eq.
apply (Hineq Hinsn).
Qed.

(* Bonus exercice x * 0 = 0 *)
Theorem mult_x_left: forall x : iota, Eq (Mult x O) O.
intros.
pose proof (ax_compr (fun x => Eq (Mult x O) O)) as [C Hieq].
apply Hieq.
apply ax_induction.
apply Hieq.
apply ax_mult_O.
intros n Hn.
apply Hieq.
pose proof (ax_mult_S n O) as Heqm.
pose proof (ax_plus_O (Mult n O)) as Heqp.
pose proof (Hieq n) as [Hieqm Heqmi].
pose proof (Hieqm Hn) as Heqmul.
apply (eq_trans (Mult (S n) O) (Mult n O) O).
pose proof (plus_x_left (Mult n O)) as Heqpm.
apply (eq_trans (Mult (S n) O) (Plus (Mult n O) O) (Mult n O)).
apply Heqm.
apply Heqpm.
apply Heqmul.
Qed.

(* Peano's predicate symbole N *)
Parameter N : iota -> Prop.

(* N(O) : O is a naturel number *)
Axiom peano_O: N O.
(* If x is a  naturel number then S(x) is a naturel number too *)
Axiom peano_S: forall x, N x -> N (S x).
(* The induction axiom on naturel numbers *)
Axiom peano_induction: forall C, In O C -> (forall x, In x C -> In (S x) C) -> forall y, N y -> In y C.
(* The induction axiom on naturel numbers with a relaxed condition (N(x) added) *)
Axiom peano_induction_N: forall C, In O C -> (forall x, N x -> In x C -> In (S x) C) -> forall y, N y -> In y C.


(* Proposition of Exervice 4.4, using the induction axiom with a relaxed condition N(x) *)
Theorem exercice_4_4_a: forall A : iota -> Prop, A O -> (forall x, N x -> A x -> A (S x)) -> forall y, N y -> A y.
Proof.
intros A HAO Hrec y HNy.
pose proof (ax_compr A) as [D Hcompr].
apply Hcompr.
(* induction axiom on 'y' *)
apply peano_induction_N.
apply Hcompr.
apply HAO.
intros x HNx Hix.
apply Hcompr.
(* induction hypothesis *)
apply Hrec.
apply HNx.
apply Hcompr.
apply Hix.
apply HNy.
Qed.

(* Same proposition of Exervice 4.4.a, using the induction axiom without the relaxed condition N(x) *)
Theorem exercice_4_4_b: forall A: iota -> Prop, A O -> (forall x, N x -> A x -> A (S x)) -> forall y, N y -> A y.
Proof.
intros A HAO Hrec y HNy.
(* The idea here is to choose the proposition A of the comprehension scheme as conjonction to have both A and N in hypothesis *)
pose proof (ax_compr (fun z => (A z) /\ (N z))) as [D Hcompr].
apply Hcompr.
(* induction axiom on 'y' *)
apply peano_induction.
apply Hcompr; split.
apply HAO.
apply peano_O.
intros x Hix.
apply Hcompr; split.
apply Hrec; apply Hcompr; apply Hix.
apply peano_S.
apply Hcompr.
apply Hix.
apply HNy.
Qed.