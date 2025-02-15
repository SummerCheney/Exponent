

(**********************************************************************)
(*  This is part of AST_AC, it is distributed under the terms of the  *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2022-2025                            *)
(*  Si Chen, Guowei Dou, Yaoshun Fu, Shukun Leng and Wensheng Yu      *)
(**********************************************************************)

(** MK_All *)

(* 读入库文件 *)

Require Export Pre_MK_Logic.

(* 分类公理图式 *)

(* 定义初始"类(Class)"，元素和集合的类型都是Class *)
Parameter Class : Type.

(* ∈：属于 x∈y : In x y *)
Parameter In : Class -> Class -> Prop.

Notation "x ∈ y" := (In x y) (at level 70).

(* 外延公理I  对于每个x与y，x=y成立之充分必要条件是对每一个z当且仅当z∈x时，z∈y *)
Axiom AxiomI : ∀ x y, x = y <-> (∀ z, z ∈ x <-> z ∈ y).

Ltac eqext := apply AxiomI; split; intros.

(* 定义1  x为一集当且仅当对于某一y，x∈y *)
Definition Ensemble x := ∃ y, x ∈ y.

Global Hint Unfold Ensemble : core.

(*分类公理图式续*)

(* {...:...} *)
Parameter Classifier : ∀ P :Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P)(at level 0).


(*分类公理II *)
Axiom AxiomII : ∀ b P, b ∈ \{ P \} <-> Ensemble b /\ (P b).

Ltac appA2G := apply AxiomII; split; eauto.

Ltac appA2H H := apply AxiomII in H as [].

(* A.3 类的初等代数 *)

(* 定理2  并集 x∪y = {z:z∈x或者z∈y} *)
Definition Union x y := \{ λ z, z ∈ x \/ z ∈ y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* 定义3  交集 x∩y = {z:z∈x同时z∈y} *)
Definition Intersection x y := \{ λ z, z ∈ x /\ z ∈ y \}.

Notation "x ∩ y" := (Intersection x y)
  (at level 60, right associativity).

(* 定理4  z∈x∪y当且仅当z∈x或者z∈y，而z∈x∩y当且仅当z∈x同时z∈y *)
Theorem MKT4 : ∀ x y z, z ∈ x \/ z ∈ y <-> z ∈ (x ∪ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Theorem MKT4' : ∀ x y z, z ∈ x /\ z ∈ y <-> z ∈ (x ∩ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Ltac deHun :=
  match goal with
   | H:  ?c ∈ ?a∪?b
     |- _ => apply MKT4 in H as [] ; deHun
   | _ => idtac
  end.

Ltac deGun :=
  match goal with
    | |-  ?c ∈ ?a∪?b => apply MKT4 ; deGun
    | _ => idtac
  end.

Ltac deHin :=
  match goal with
   | H:  ?c ∈ ?a∩?b
     |- _ => apply MKT4' in H as []; deHin
   | _ => idtac  
  end.

Ltac deGin :=
  match goal with
    | |- ?c ∈ ?a∩?b => apply MKT4'; split; deGin
    | _ => idtac
  end.

(* 定理5  x∪x=x同时x∩x=x *)
Theorem MKT5 : ∀ x, x ∪ x = x.
Proof.
  intros; eqext; deGun; deHun; auto.
Qed.

Theorem MKT5' : ∀ x, x ∩ x = x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* 定理6  x∪y=y∪x同时x∩y=y∩x *)
Theorem MKT6 : ∀ x y, x ∪ y = y ∪ x.
Proof.
  intros; eqext; deHun; deGun; auto.
Qed.

Theorem MKT6' : ∀ x y, x ∩ y = y ∩ x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* 定理7  (x∪y)∪z=x∪(y∪z)同时(x∩y)∩z=x∩(y∩z) *)
Theorem MKT7 : ∀ x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; eqext; deHun; deGun; auto;
  [right|right|left|left]; deGun; auto.
Qed.

Theorem MKT7' : ∀ x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; eqext; deGin; deHin; auto.
Qed.

(* 定理8  x∩(y∪z)=(x∩y)∪(x∩z)同时x∪(y∩z)=(x∪y)∩(x∪z) *)
Theorem MKT8 : ∀ x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; eqext; deHin; deHun; deGun; deGin; [left|right|..];
  deHin; deHun; deGun; deGin; auto.
Qed.

Theorem MKT8' : ∀ x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; eqext; deHin; deHun; deGin; repeat deGun; deHin; auto.
  right; deGin; auto.
Qed.

(* 定义9  x∉y当且仅当x∈y不真 *)
Definition NotIn x y := ~ (x ∈ y).

Notation "x ∉ y" := (NotIn x y)(at level 10).

(* 定义10  ¬x={y：y∉x} *)
Definition Complement x := \{ λ y, y ∉ x \}.

Notation "¬ x" := (Complement x)(at level 5, right associativity).

(* 定理11  ¬ (¬ x) = x *)
Theorem MKT11: ∀ x, ¬ (¬ x) = x.
Proof.
  intros; eqext.
  - appA2H H. Absurd. elim H0. appA2G.
  - appA2G. intro. appA2H H0; auto.
Qed.

(* 定理12  De Morgan   ¬(x∪y)=(¬x)∩(¬y)同时¬(x∩y)=(¬x)∪(¬y) *)
Theorem MKT12 : ∀ x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; eqext.
  - appA2H H; deGin; appA2G; intro; apply H0; deGun; auto.
  - deHin. appA2H H; appA2H H0. appA2G. intro. deHun; auto.
Qed.

Theorem MKT12' : ∀ x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros. rewrite <-(MKT11 x),<-(MKT11 y),<-MKT12.
  repeat rewrite MKT11; auto.
Qed.

(* 定义13  x ~ y=x∩(¬ y) *)
Definition Setminus x y := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y)(at level 50, left associativity).

Fact setminP : ∀ z x y, z ∈ x -> ~ z ∈ y -> z ∈ (x ~ y).
Proof.
  intros. appA2G. split; auto. appA2G.
Qed.

Global Hint Resolve setminP : core.

Fact setminp : ∀ z x y, z ∈ (x ~ y) -> z ∈ x /\ ~ z ∈ y.
Proof.
  intros. appA2H H. destruct H0. appA2H H1; auto.
Qed.

(* 定理14  x∩(y ~ z)=(x∩y) ~ z *)
Theorem MKT14 : ∀ x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Setminus; rewrite MKT7'; auto.
Qed.

(* 定义85  x≠y 当且仅当 x=y 不真 *)
Definition Inequality (x y :Class) := ~ (x = y).

Notation "x ≠ y" := (Inequality x y)(at level 70).

(* 定义15  Φ={x:x≠x} *)
Definition Φ := \{λ x, x ≠ x \}.

(* 定理16  x∉Φ *)
Theorem MKT16 : ∀ {x}, x ∉ Φ.
Proof.
  intros; intro. apply AxiomII in H; destruct H; auto.
Qed.

Ltac emf :=
  match goal with
    H:  ?a ∈ Φ
    |- _ => destruct (MKT16 H)
  end.

Ltac eqE := eqext; try emf; auto.

Ltac feine z := destruct (@ MKT16 z).

(* 定理17  Φ∪x=x同时Φ∩x=Φ *)
Theorem MKT17 : ∀ x, Φ ∪ x = x.
Proof.
  intros; eqext; deHun; deGun; auto; emf.
Qed.

Theorem MKT17' : ∀ x, Φ ∩ x = Φ.
Proof.
  intros. eqE. deHin; auto.
Qed.

(* 定义18  全域 μ={x:x=x} *)
Definition μ := \{ λ x, x = x \}.

(* 定理19  x∈μ当且仅当x是一个集  *)
Theorem MKT19 : ∀ x, x ∈ μ <-> Ensemble x.
Proof.
  split; intros; eauto. appA2G.
Qed.

Theorem MKT19a : ∀ x, x ∈ μ -> Ensemble x.
Proof.
  intros. apply MKT19; auto.
Qed.

Theorem MKT19b : ∀ x, Ensemble x -> x ∈ μ.
Proof.
  intros. apply MKT19; auto.
Qed.

Global Hint Resolve MKT19a MKT19b : core.

(* 定理20  x∪μ=μ同时x∩μ=x *)
Theorem MKT20 : ∀ x, x ∪ μ = μ.
Proof.
  intros; eqext; deHun; deGun; eauto.
Qed.

Theorem MKT20' : ∀ x, x ∩ μ = x.
Proof.
  intros; eqext; deHin; deGin; eauto.
Qed.

(* 定理21  ¬Φ=μ同时¬μ=Φ *)
Theorem MKT21 : ¬ Φ = μ.
Proof.
  eqext; appA2G. apply MKT16.
Qed.

Theorem MKT21' : ¬ μ = Φ.
Proof.
  rewrite <-MKT11,MKT21; auto.
Qed.

(* 定义22  ∩x={z:对于每个y，如果y∈x，则z∈y} *)
Definition Element_I x := \{ λ z, ∀ y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x)(at level 66).

(* 定义23  ∪x={z:对于某个y，z∈y同时y∈x} *)
Definition Element_U x := \{ λ z, ∃ y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x)(at level 66).

Ltac deHex1 :=
  match goal with
    H: ∃ x, ?P 
    |- _ => destruct H as []
  end.

Ltac rdeHex := repeat deHex1; deand.

(* 定理24  ∩Φ=μ同时∪Φ=Φ *)
Theorem MKT24 : ∩Φ = μ.
Proof.
  eqext; appA2G; intros; emf.
Qed.

Theorem MKT24' : ∪Φ = Φ.
Proof.
  eqE. appA2H H. rdeHex. emf.
Qed.

(* 定义25  x⊂y 当且仅当对于每个z，如果z∈x，则z∈y *)
Definition Included x y :=  ∀ z, z ∈ x -> z ∈ y.

Notation "x ⊂ y" := (Included x y)(at level 70).

(* 定理26  Φ⊂x同时x⊂μ *)
Theorem MKT26 : ∀ x, Φ ⊂ x.
Proof.
  unfold Included; intros; emf.
Qed.

Theorem MKT26' : ∀ x, x ⊂ μ.
Proof.
  unfold Included; intros; eauto.
Qed.

Theorem MKT26a : ∀ x, x ⊂ x.
Proof.
  unfold Included; intros; auto.
Qed.

Global Hint Resolve MKT26 MKT26' MKT26a : core.

Fact ssubs : ∀ {a b z}, z ⊂ (a ~ b) -> z ⊂ a.
Proof.
  unfold Included; intros. apply H in H0. appA2H H0; tauto.
Qed.

Global Hint Immediate ssubs : core.

Fact esube : ∀ {z}, z ⊂ Φ -> z = Φ.
Proof. intros. eqE. Qed.

(* 定理27  x=y当且仅当x⊂y同时y⊂x *)
Theorem MKT27 : ∀ x y, (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  split; intros; subst; [destruct H; eqext|split]; auto.
Qed.

(* 定理28  如果x⊂y且y⊂z，则x⊂z *)
Theorem MKT28 : ∀ {x y z}, x ⊂ y -> y ⊂ z -> x ⊂ z.
Proof.
  unfold Included; intros; auto.
Qed.

(* 定理29  x⊂y当且仅当x∪y=y *)
Theorem MKT29 : ∀ x y, x ∪ y = y <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H; deGun|eqext; deGun; deHun]; auto.
Qed.

(* 定理30  x⊂y当且仅当x∩y=x *)
Theorem MKT30 : ∀ x y, x ∩ y = x <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H in H0; deHin|eqext; deGin; deHin]; auto.
Qed.

(* 定理31  如果x⊂y,则∪x⊂∪y同时∩y⊂∩x *)
Theorem MKT31 : ∀ x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  split; red; intros; appA2H H0; rdeHex; appA2G.
Qed.

(* 定理32  如果x∈y,则x⊂∪y同时∩y⊂x *)
Theorem MKT32 : ∀ x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  split; red; intros; [appA2G|appA2H H0; auto].
Qed.

(*A.4 集的存在性 *)

(* 子集公理III 如果x是一个集，存在一个集y使得对于每个z，假定z⊂x，则z∈y *)
Axiom AxiomIII : ∀ {x}, Ensemble x
  -> ∃ y, Ensemble y /\ (∀ z, z ⊂ x -> z ∈ y).

(* 定理33  如果x是一个集同时z⊂x，则z是一个集 *)
Theorem MKT33 : ∀ x z, Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros. destruct (AxiomIII H) as [y []]; eauto.
Qed.

(* 定理34  0=∩μ同时∪μ =μ *)
Theorem MKT34 : Φ = ∩μ.
Proof.
  eqE. appA2H H. apply H0. appA2G. eapply MKT33; eauto.
Qed.

Theorem MKT34' : μ = ∪μ.
Proof.
  eqext; eauto. destruct (@ AxiomIII z) as [y []]; eauto. appA2G.
Qed.

(* 定理35  如果x≠0，则∩x是一个集 *)
Lemma NEexE : ∀ x, x ≠ Φ <-> ∃ z, z∈x.
Proof.
  split; intros.
  - Absurd. elim H; eqext; try emf. elim H0; eauto.
  - intro; subst. destruct H. emf.
Qed.

Ltac NEele H := apply NEexE in H as [].

Theorem MKT35 : ∀ x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros. NEele H. eapply MKT33; eauto. apply MKT32; auto.
Qed.

(* 定义36  pow(x)={y:y⊂x} *)
Definition PowerClass x := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerClass x)
  (at level 0, right associativity).

(* 定理37  u=pow(u) *)
Theorem MKT37 : μ = pow(μ).
Proof.
  eqext; appA2G; eauto.
Qed.

(* 定理38  如果x是一个集,则pow(x)是一个集*)
Theorem MKT38a : ∀ {x}, Ensemble x -> Ensemble pow(x).
Proof.
  intros. New (AxiomIII H). rdeHex. eapply MKT33; eauto.
  red; intros. appA2H H2; auto.
Qed.

Theorem MKT38b : ∀ {x}, Ensemble x -> (∀ y, y ⊂ x <-> y ∈ pow(x)).
Proof.
  split; intros; [appA2G; eapply MKT33; eauto|appA2H H0; auto].
Qed.

(* 定理39  μ不是一个集 *)

(* 一个不是集的类 *)
Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  TF (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \}).
  - New H. appA2H H; auto.
  - intro. apply H,AxiomII; auto.
Qed.

Theorem MKT39 : ~ Ensemble μ.
Proof.
  intro. apply Lemma_N. eapply MKT33; eauto.
Qed.

(* 定义40  [x]={z:如果x∈μ，则z=x} *)
Definition Singleton x := \{ λ z, x ∈ μ -> z = x \}.

Notation "[ x ]" := (Singleton x)(at level 0, right associativity).

Fact singlex : ∀ x, Ensemble x -> x ∈ [x].
Proof.
  intros. appA2G.
Qed.

Global Hint Resolve singlex : core.

(* 定理41  如果x是一个集，则对于每个y，y∈[x]当且仅当y=x *)
Theorem MKT41 : ∀ x, Ensemble x -> (∀ y, y ∈ [x] <-> y = x).
Proof.
  split; intros; [appA2H H0; auto|subst; appA2G].
Qed.

Ltac eins H := apply MKT41 in H; subst; eauto.

(* 定理42  如果x是一个集，则[x]是一个集 *)
Theorem MKT42 : ∀ x, Ensemble x -> Ensemble [x].
Proof.
  intros. New (MKT38a H). eapply MKT33; eauto.
  red; intros. eins H1. appA2G.
Qed.

Global Hint Resolve MKT42 : core.

(* 定理43  [x]=μ当且仅当x不是一个集*)
Theorem MKT43 : ∀ x, [x] = μ <-> ~ Ensemble x.
Proof.
  split; intros.
  - intro. apply MKT39. rewrite <-H; auto.
  - eqext; eauto. appA2G; intro; elim H; auto.
Qed.

(* 定理42'  如果[x]是一个集，则x是一个集 *)
Theorem MKT42' : ∀ x, Ensemble [x] -> Ensemble x.
Proof.
  intros. Absurd. apply MKT43 in H0.
  elim MKT39. rewrite <-H0; auto.
Qed.

(* 定理44  如果x是一个集，则∩[x]=x同时∪[x]=x；如果x不是一个集，则∩[x]=0同时∪[x]=u *)
Theorem MKT44 : ∀ {x}, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  split; intros; eqext; try appA2G.
  - appA2H H0. apply H1; auto.
  - intros. eins H1.
  - appA2H H0. rdeHex. eins H2; subst; auto.
Qed.

Theorem MKT44' : ∀ x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros. apply MKT43 in H.
  rewrite H; split; symmetry; [apply MKT34|apply MKT34'].
Qed.

(* 并的公理IV 如果x是一个集同时y是一个集，则x∪y也是一个集*)
Axiom AxiomIV : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble (x ∪ y).

Corollary AxiomIV': ∀ x y, Ensemble (x ∪ y)
  -> Ensemble x /\ Ensemble y.
Proof.
  split; intros; eapply MKT33; eauto; red; intros; deGun; auto.
Qed.

(* 定义45  [x|y]=[x]∪[y] *)
Definition Unordered x y := [x] ∪ [y].

Notation "[ x | y ]" := (Unordered x y)(at level 0).

(* 定理46  如果x是一个集同时y是一个集，则[x|y]是一个集，同时z∈[x|y] 当且仅当 z=x或者z=y;
          [x|y]=μ 当且仅当 x不是一个集或者y不是一个集 *)
Theorem MKT46a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble [x|y].
Proof.
  intros; apply AxiomIV; apply MKT42; auto.
Qed.

Global Hint Resolve MKT46a : core.

Theorem MKT46b : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∀ z, z ∈ [x|y] <-> (z = x \/ z = y)).
Proof.
  split; unfold Unordered; intros.
  - deHun; eins H1.
  - deGun. destruct H1; subst; auto.
Qed.

Theorem MKT46' : ∀ x y, [x|y] = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  split; intros.
  - Absurd. apply notandor in H0 as []. elim MKT39.
    rewrite <-H. apply MKT46a; apply NNPP; auto.
  - unfold Unordered; destruct H; apply MKT43 in H;
    rewrite H; [rewrite MKT6|]; apply MKT20.
Qed.

(* 定理47  如果x与y是两个集，则∩[x|y]=x∩y同时∪[x|y]=x∪y; 如果x或者y不是一个集，则∩[x|y]=0同时∪[x|y]=u *)
Theorem MKT47a : ∀ x y, Ensemble x -> Ensemble y -> ∩[x|y] = x ∩ y.
Proof.
  intros; unfold Unordered; eqext; appA2H H1; appA2G.
  - split; apply H2; deGun; auto.
  - destruct H2; intros. deHun; eins H4.
Qed.

Theorem MKT47b : ∀ x y, Ensemble x -> Ensemble y
  -> ∪[x|y] = x ∪ y.
Proof.
  intros; unfold Unordered; eqext; appA2H H1; appA2G.
  - rdeHex. deHun; eins H3.
  - destruct H2; [exists x|exists y]; split; auto;
    apply MKT46b; auto. 
Qed.

Theorem MKT47' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> (∩[x|y] = Φ) /\ (∪[x|y] = μ).
Proof.
  intros. apply MKT46' in H. rewrite H; split; symmetry;
  [apply MKT34|apply MKT34'].
Qed.

(* A.5 序偶：关系 *)

(* 定义48  [x,y] = [[x]|[x|y]] *)
Definition Ordered x y:= [[x]|[x|y]].

Notation "[ x , y ]" := (Ordered x y)(at level 0).

Theorem MKT49a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble [x,y].
Proof.
  intros; unfold Ordered, Unordered.
  apply AxiomIV; [|apply MKT42,AxiomIV]; auto.
Qed.

Global Hint Resolve MKT49a : core.

Theorem MKT49b : ∀ x y, Ensemble [x,y] -> Ensemble x /\ Ensemble y.
Proof.
  intros. apply AxiomIV' in H as []. apply MKT42',
  AxiomIV' in H0 as []. split; apply MKT42'; auto.
Qed.

Theorem MKT49c1 : ∀ {x y}, Ensemble [x,y] -> Ensemble x.
Proof.
  intros. apply MKT49b in H; tauto.
Qed.

Theorem MKT49c2 : ∀ {x y}, Ensemble [x,y] -> Ensemble y.
Proof.
  intros. apply MKT49b in H; tauto.
Qed.

Ltac ope1 :=
  match goal with
    H: Ensemble [?x,?y]
    |- Ensemble ?x => eapply MKT49c1; eauto
  end.

Ltac ope2 :=
  match goal with
    H: Ensemble [?x,?y]
    |- Ensemble ?y => eapply MKT49c2; eauto
  end.

Ltac ope3 :=
  match goal with
    H: [?x,?y] ∈ ?z
    |- Ensemble ?x => eapply MKT49c1; eauto
  end.

Ltac ope4 :=
  match goal with
    H: [?x,?y] ∈ ?z
    |- Ensemble ?y => eapply MKT49c2; eauto
  end.

Ltac ope := try ope1; try ope2; try ope3; try ope4.

Theorem MKT49' : ∀ x y, ~ Ensemble [x,y] -> [x,y] = μ.
Proof.
  intros. apply MKT46'. apply notandor; intros [].
  apply H,AxiomIV; apply MKT42; auto.
Qed.

Fact subcp1 : ∀ x y, x ⊂ (x ∪ y).
Proof.
  unfold Included; intros. deGun; auto.
Qed.

Global Hint Resolve subcp1 : core.

(* 定理50  如果x与y均为集,则∪[x,y]=[x|y],∩[x,y]=[x],∪∩[x,y]=x,∩∩[x,y]=x,∪∪[x,y]=x∪y,∩∪[x,y]=x∩y如果x或者y不是一个集,则∪∩[x,y]=Φ,∩∩[x,y]=Φ,∪∪[x,y]=Φ,∩∪[x,y]=Φ *)
Lemma Lemma50a : ∀ x y, Ensemble x -> Ensemble y -> ∪[x,y] = [x|y].
Proof.
  intros; unfold Ordered. rewrite MKT47b; auto.
  apply MKT29; unfold Unordered; auto.
Qed.

Lemma Lemma50b : ∀ x y, Ensemble x -> Ensemble y -> ∩[x,y] = [x].
Proof.
  intros; unfold Ordered. rewrite MKT47a; auto.
  apply MKT30; unfold Unordered; auto.
Qed.

Theorem MKT50 : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\ (∪(∩[x,y]) = x)
    /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  repeat split; intros; repeat rewrite Lemma50a;
  repeat rewrite Lemma50b; auto; 
  [apply MKT44|apply MKT44|apply MKT47b|apply MKT47a]; auto.
Qed.

Lemma Lemma50' : ∀ (x y: Class), ~ Ensemble x \/ ~ Ensemble y
  -> ~ Ensemble [x] \/ ~ Ensemble [x | y].
Proof.
  intros. elim H; intros. 
  - left; apply MKT43 in H0; auto. rewrite H0; apply MKT39; auto.
  - right; apply MKT46' in H; auto. rewrite H; apply MKT39; auto.
Qed.

Theorem MKT50' : ∀ {x y}, ~ Ensemble x \/ ~ Ensemble y
  -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ) /\ (∪(∪[x,y]) = μ)
    /\ (∩(∪[x,y]) = Φ).
Proof.
  intros. apply Lemma50',MKT47' in H as [].
  unfold Ordered. repeat rewrite H; repeat rewrite H0; repeat split;
  [apply MKT24'|apply MKT24|rewrite <-MKT34'|rewrite MKT34]; auto.
Qed.

(* 定义51  z的1st坐标=∩∩z *)
Definition First z := ∩(∩z).

(* 定义52  z的2nd坐标=(∩∪z)∪(∪∪z) ~ (∪∩z) *)
Definition Second z := (∩ ∪ z) ∪ ((∪(∪z)) ~ (∪(∩z))).

(* 定理53  μ的2nd坐标=μ *)
Theorem MKT53 : Second μ = μ.
Proof.
  intros; unfold Second, Setminus.
  repeat rewrite <-MKT34'; repeat rewrite <-MKT34.
  rewrite MKT24',MKT17,MKT21,MKT5'; auto.
Qed.

(* 定理54  如果x与y均为集,[x,y]的1st坐标=x同时[x,y]的2nd坐标=y
          如果x或者y不是一个集，则[x,y]的1st坐标=μ,同时[x,y]的2nd坐标=μ *)
Theorem MKT54a : ∀ x y, Ensemble x -> Ensemble y
  -> First [x,y] = x.
Proof.
  intros; unfold First. apply MKT50; auto.
Qed.

Theorem MKT54b : ∀ x y, Ensemble x -> Ensemble y
  -> Second [x,y] = y.
Proof.
  intros; unfold Second. New (MKT50 H H0). deand.
  rewrite H6,H5,H3. eqext.
  - appA2H H7. deor; [appA2H H8; tauto|].
    apply setminp in H8 as []. appA2H H8; tauto.
  - appA2G. TF (z ∈ x); [left; appA2G|].
    right. apply setminP; auto. appA2G.
Qed.

Theorem MKT54' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> First [x,y] = μ /\ Second [x,y] = μ.
Proof.
  intros. New (MKT50' H). deand. unfold First, Second; split; auto.
  rewrite H3,H2,H0,MKT17. unfold Setminus. 
  rewrite MKT6',MKT20'. apply MKT21.
Qed.

(* 定理55  如果x与y均为集,同时[x,y]=[u,v],则z=x同时y=v *)
Theorem MKT55 : ∀ x y u v, Ensemble x -> Ensemble y
  -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  split; intros; [|destruct H1; subst; auto].
  assert (Ensemble [x,y]); auto. rewrite H1 in H2.
  apply MKT49b in H2 as []. rewrite <-(MKT54a x y),H1,
  <-(MKT54b x y),H1,MKT54a,MKT54b; auto.
Qed.

Fact Pins : ∀ a b c d, Ensemble c -> Ensemble d
  -> [a,b] ∈ [[c,d]] -> a = c /\ b = d.
Proof.
  intros. eins H1. symmetry in H1. apply MKT55 in H1 as []; auto.
Qed.

Ltac pins H := apply Pins in H as []; subst; eauto.

Fact Pinfus : ∀ a b f x y, Ensemble x -> Ensemble y
  -> [a,b] ∈ (f ∪ [[x,y]]) -> [a,b] ∈ f \/ (a = x /\ b = y).
Proof.
  intros. deHun; auto. pins H1. 
Qed.

Ltac pinfus H := apply Pinfus in H as [?|[]]; subst; eauto.

Ltac eincus H := apply AxiomII in H as [_ [H|H]]; try eins H; auto.

(* 定义56  r是一个关系当且仅当对于r的每个元z存在x与y使得z=[x,y]; 一个关系是一个类，它的元为序偶 *)
Definition Relation r := ∀ z, z ∈ r -> ∃ x y, z = [x,y].

(* { (x,y) : ... } *)
Notation "\{\ P \}\" := \{ λ z, ∃ x y, z = [x,y] /\ P x y \}
  (at level 0).

Ltac PP H a b := apply AxiomII in H as [? [a [b []]]]; subst.

Fact AxiomII' : ∀ a b P,
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).
Proof.
  split; intros.
  - PP H x y. apply MKT55 in H0 as []; subst; auto; ope.
  - destruct H. appA2G.
Qed.

Ltac appoA2G := apply AxiomII'; split; eauto.

Ltac appoA2H H := apply AxiomII' in H as [].

(* 定义57 r∘s={u:对于某个x，某个y及某个z,u=[x,z],[x,y]∈s同时[y,z]∈r},类r∘s是r与s的合成 *)
Definition Composition r s := \{\ λ x z, ∃ y, [x,y] ∈ s
  /\ [y,z] ∈ r \}\.

Notation "r ∘ s" := (Composition r s)(at level 50).

(* 定理58  (r∘s)∘t=r∘(s∘t) *)
Theorem MKT58 : ∀ r s t, (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros; eqext.
  - PP H a b. rdeHex. appoA2H H1. rdeHex.
    appoA2G. exists x0; split; auto. appoA2G. apply MKT49a; ope.
  - PP H a b. rdeHex. appoA2H H0. rdeHex.
    appoA2G. exists x0; split; auto. appoA2G. apply MKT49a; ope.
Qed.

(* 定理59  r∘(s∪t)=r∘s∪r∘t,同时r∘(s∩t)⊂r∩s∘r∩t *)
Theorem MKT59 : ∀ r s t, Relation r -> Relation s
  -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t)
    /\ r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  split; try red; intros; try eqext.
  - PP H1 a b. rdeHex. deHun; deGun; [left|right]; appoA2G.
  - deHun; PP H1 a b; rdeHex; appoA2G; 
    exists x; split; auto; deGun; auto.
  - PP H1 a b. rdeHex. deHin. deGin; appoA2G.
Qed.

(* 定义60  r ⁻¹={[x,y]:[y,x]∈r} *)
Definition Inverse r := \{\ λ x y, [y,x]∈r \}\.

Notation "r ⁻¹" := (Inverse r)(at level 5).

Fact invp1 : ∀ a b f, [b,a] ∈ f⁻¹ <-> [a,b] ∈ f.
Proof.
  split; intros; [appoA2H H; tauto|appoA2G; apply MKT49a; ope].
Qed.

Fact uiv : ∀ a b, (a ∪ b)⁻¹ = a⁻¹ ∪ b⁻¹.
Proof.
  intros. eqext.
  - PP H x y. deHun; apply invp1 in H0; deGun; auto.
  - deHun; PP H x y; appoA2G; deGun; auto.
Qed.

Fact iiv : ∀ a b, (a ∩ b)⁻¹ = a⁻¹ ∩ b⁻¹.
Proof.
  intros. eqext.
  - PP H x y. deHin; deGin; apply invp1; auto.
  - deHin; PP H x y. apply invp1; deGin; [|apply invp1]; auto.
Qed.

Fact siv : ∀ a b, Ensemble a -> Ensemble b -> [[a,b]]⁻¹ = [[b,a]].
Proof.
  intros. eqext.
  - PP H1 x y. pins H3.
  - eins H1. appoA2G.
Qed.

(* 定理61  (r ⁻¹)⁻¹=r *)
Theorem MKT61 : ∀ r, Relation r -> (r⁻¹)⁻¹ = r.
Proof.
  intros; eqext.
  - PP H0 a b. appoA2H H2; auto.
  - New H0. apply H in H0 as [? [?]]; subst.
    appoA2G. apply invp1; auto.
Qed.

(* 定理62  (r∘s)⁻¹=(s⁻¹)∘(r⁻¹) *)
Theorem MKT62 : ∀ r s, (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; eqext.
  - PP H a b. appoA2H H1. rdeHex.
    appoA2G. exists x. split; appoA2G; apply MKT49a; ope.
  - PP H a b. rdeHex. appoA2H H0. appoA2H H1.
    apply invp1. appoA2G. apply MKT49a; ope.
Qed.

(* A.6 函数 *)

(* 定义63 f是一个函数当且仅当f是一个关系同时对每个x，每个y，每个z，如果 [x,y]∈f 且
   [x，z]∈f，则 y=z。*)
Definition Function f  := Relation f
  /\ (∀ x y z, [x,y] ∈ f -> [x,z] ∈ f -> y = z).

Fact opisf : ∀ a b, Ensemble a -> Ensemble b -> Function ([[a,b]]).
Proof.
  split; [red|]; intros; [eins H1|pins H1; pins H2].
Qed.

(* 定理64 如果f是一个函数同时g是一个函数，则 f∘g 也是一个函数 *)
Fact PisRel : ∀ P, Relation \{\ P \}\.
Proof.
  unfold Relation; intros. PP H a b; eauto.
Qed.

Global Hint Resolve PisRel : core.

Theorem MKT64 : ∀ f g, Function f -> Function g -> Function (f ∘ g).
Proof.
  split; intros; unfold Composition; auto.
  appoA2H H1. appoA2H H2. rdeHex. destruct H0.
  apply H with x0; auto. rewrite (H7 x x0 x1); auto.
Qed.

(* 定义65 f的定义域={x：对于某个y，[x，y]∈f} *)
Definition Domain f := \{ λ x, ∃ y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

Corollary Property_dom : ∀ {x y f}, [x,y] ∈ f -> x ∈ dom(f).
Proof.
  intros. appA2G. ope.
Qed.

(* 定义66 f的值域={y：对于某个x，[x，y]∈f} *)
Definition Range f := \{ λ y, ∃ x, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

Corollary Property_ran : ∀ {x y f}, [x,y] ∈ f -> y ∈ ran(f).
Proof.
  intros. appA2G. ope.
Qed.

Fact deqri : ∀ f, dom(f) = ran(f⁻¹).
Proof.
  intros; eqext; appA2H H; rdeHex;
  [apply invp1 in H0|apply ->invp1 in H0]; appA2G.
Qed.

Fact reqdi : ∀ f, ran(f) = dom(f⁻¹).
Proof.
  intros; eqext; appA2H H; rdeHex; 
  [apply invp1 in H0|apply ->invp1 in H0]; appA2G.
Qed.

Fact subdom : ∀ {x y}, x ⊂ y -> dom(x) ⊂ dom(y).
Proof.
  unfold Included; intros. appA2H H0. rdeHex. appA2G.
Qed.

Fact undom : ∀ f g, dom(f ∪ g) = dom(f) ∪ dom(g).
Proof.
  intros; eqext.
  - appA2H H. rdeHex. deHun; deGun; [left|right]; appA2G.
  - deHun; appA2H H; rdeHex;
    appA2G; exists x; deGun; auto.
Qed.

Fact unran : ∀ f g, ran(f ∪ g) = ran(f) ∪ ran(g).
Proof.
  intros; eqext.
  - appA2H H. rdeHex. deHun; deGun; [left|right]; appA2G.
  - deHun; apply AxiomII in H as [? []];
    appA2G; exists x; deGun; auto.
Qed.

Fact domor : ∀ u v, Ensemble u -> Ensemble v -> dom([[u,v]]) = [u].
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. pins H2.
  - eins H1. appA2G.
Qed.

Fact ranor : ∀ u v, Ensemble u -> Ensemble v -> ran([[u,v]]) = [v].
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. pins H2.
  - eins H1. appA2G.
Qed.

Fact fupf : ∀ f x y, Function f -> Ensemble x -> Ensemble y
  -> ~ x ∈ dom(f) -> Function (f ∪ [[x,y]]).
Proof.
  repeat split; try red; intros.
  - destruct H. deHun; auto. eins H3.
  - pinfus H3; pinfus H4; [eapply H; eauto|..];
    elim H2; eapply Property_dom; eauto.
Qed.

Fact dos1 : ∀ {f x} y, Function f -> [x,y] ∈ f
  -> dom(f ~ [[x,y]]) = dom(f) ~ [x].
Proof.
  intros. eqext; appA2H H1; destruct H2.
  - apply setminp in H2 as []. New H2. apply Property_dom in H2.
    apply setminP; auto. intro. eins H5; ope.
    eapply H in H0; eauto. subst. elim H3; eauto.
  - appA2H H2. appA2H H3. destruct H4. appA2G. exists x0.
    apply setminP; auto. intro. pins H6; ope. 
Qed.

Fact ros1 : ∀ {f x y}, Function f⁻¹ -> [x,y] ∈ f
  -> ran(f ~ [[x,y]]) = ran(f) ~ [y].
Proof.
  intros. eqext; appA2H H1; destruct H2.
  - apply setminp in H2 as []. New H2. apply Property_ran in H2.
    apply setminP; auto. intro. eins H5; ope.
    New H0. apply invp1 in H0. apply invp1 in H4.
    eapply H in H0; eauto. subst. elim H3; eauto.
  - appA2H H2. appA2H H3. destruct H4. appA2G. exists x0.
    apply setminP; auto. intro. pins H6; ope. 
Qed.

(* 定理67 μ的定义域=μ同时μ的值域=μ *)
Theorem MKT67a: dom(μ) = μ.
Proof.
  eqext; eauto. appA2G. exists z. appA2G.
Qed.

Theorem MKT67b: ran(μ) = μ.
Proof.
  eqext; eauto. appA2G. exists z. appA2G.
Qed.

(* 定义68 f(x)=∩{y:[x,y]∈f} *)
Definition Value f x := ∩(\{ λ y, [x,y] ∈ f \}).

Notation "f [ x ]" := (Value f x)(at level 5).

Theorem MKT69a : ∀ {x f}, x ∉ dom(f) -> f[x] = μ.
Proof.
  intros. unfold Value. rewrite <-MKT24. f_equal.
  eqext; try emf. appA2H H0. elim H. eapply Property_dom; eauto.
Qed.

Theorem MKT69b : ∀ {x f}, x ∈ dom(f) -> f[x] ∈ μ.
Proof.
  intros. appA2H H. destruct H0. apply MKT19,MKT35,NEexE.
  exists x0. appA2G. ope.
Qed.

Theorem MKT69a' : ∀ {x f}, f[x] = μ -> x ∉ dom(f).
Proof.
  intros. intro. elim MKT39. New (MKT69b H0). rewrite <-H ; eauto.
Qed.

Theorem MKT69b' : ∀ {x f}, f[x] ∈ μ -> x ∈ dom(f).
Proof.
  intros. Absurd. apply MKT69a in H0. rewrite H0 in H.
  elim MKT39; eauto.
Qed.

Corollary Property_Fun : ∀ y f x, Function f
  -> [x,y] ∈ f -> y = f[x].
Proof.
  intros; destruct H. eqext.
  - appA2G; intros. appA2H H3. rewrite (H1 _ _ _ H4 H0); auto.
  - appA2H H2. apply H3. appA2G. ope.
Qed.

Lemma uvinf : ∀ z a b f, ~ a ∈ dom(f) -> Ensemble a -> Ensemble b
  -> (z ∈ dom(f) -> (f ∪ [[a,b]])[z] = f[z]).
Proof.
  intros; eqext; appA2H H3; appA2G; intros.
  - apply H4. appA2H H5. appA2G. deGun; auto.
  - apply H4; appA2H H5. appA2G. pinfus H6. tauto.
Qed.

Lemma uvinp : ∀ a b f, ~ a ∈ dom(f) -> Ensemble a -> Ensemble b
  -> (f ∪ [[a,b]])[a] = b.
Proof.
  intros; apply AxiomI; split; intros.
  - appA2H H2. apply H3. appA2G. deGun; auto.
  - appA2G; intros. appA2H H3. pinfus H4. elim H.
    eapply Property_dom; eauto.
Qed.

Fact Einr : ∀ {f z}, Function f -> z ∈ ran(f)
  -> ∃ x, x ∈ dom(f) /\ z = f[x].
Proof.
  intros. appA2H H0. destruct H1. New H1. apply Property_dom in H1.
  apply Property_Fun in H2; eauto.
Qed.

Ltac einr H := New H; apply Einr in H as [? []]; subst; auto.

(* 定理70 如果f是一个函数，则f={[x,y]:y=f[x]} *)
Theorem MKT70 : ∀ f, Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; eqext.
  - New H0. apply H in H0 as [? [?]]. subst. appoA2G.
    apply Property_Fun; auto.
  - PP H0 a b. apply MKT49b in H0 as [].
    apply MKT19,MKT69b' in H1. appA2H H1. destruct H2.
    rewrite <-(Property_Fun x); auto.
Qed.

(* 值的性质 一 *)
Corollary Property_Value : ∀ {f x}, Function f -> x ∈ dom(f)
  -> [x,f[x]] ∈ f.
Proof.
  intros. rewrite MKT70; auto. New (MKT69b H0). appoA2G.
Qed.

Fact subval : ∀ {f g}, f ⊂ g -> Function f -> Function g
  -> ∀ u, u ∈ dom(f) -> f[u] = g[u].
Proof.
  intros. apply Property_Fun,H,Property_Value; auto.
Qed.

(* 值的性质 二 *)
Corollary Property_Value' : ∀ f x, Function f -> f[x] ∈ ran(f)
  -> [x,f[x]] ∈ f.
Proof.
  intros. rewrite MKT70; auto. appoA2G. apply MKT49a; eauto.
  exists dom(f). apply MKT69b', MKT19; eauto.
Qed.

Corollary Property_dm : ∀ {f x}, Function f -> x ∈ dom(f)
  -> f[x] ∈ ran(f).
Proof.
  intros. apply Property_Value in H0; auto. appA2G. ope. 
Qed.

(* 定理71 如果f和g都是函数，则f=g的充要条件是对于每个x，f[x]=g[x] *)
Theorem MKT71 : ∀ f g, Function f -> Function g
  -> (f = g <-> ∀ x, f[x] = g[x]).
Proof.
  split; intros; subst; auto.
  rewrite (MKT70 f),(MKT70 g); auto. eqext; PP H2 a b; appoA2G.
Qed.

(* 代换公理 V 如果f是一个函数同时f的定义域是一个集，则f的值域是一个集 *)
Axiom AxiomV : ∀ {f}, Function f -> Ensemble dom(f)
  -> Ensemble ran(f).

(* 合并公理 VI 如果x是一个集，则 ∪x 也是一个集 *)
Axiom AxiomVI : ∀ x, Ensemble x -> Ensemble (∪x).

(* 定义72 x × y={[u,v]:u∈x/\v∈y} *)
Definition Cartesian x y:= \{\ λ u v, u ∈ x /\ v ∈ y \}\.

Notation "x × y" := (Cartesian x y)
  (at level 2, right associativity).

Ltac xo :=
  match goal with
    |- Ensemble ([?a, ?b]) => try apply MKT49a
  end.

Ltac rxo := eauto; repeat xo; eauto.

(* 定理73 如果u与y均为集，则[u]×y也是集*)
Lemma Ex_Lemma73 : ∀ {u y}, Ensemble u -> Ensemble y
  -> let f:= \{\ λ w z, w ∈ y /\ z = [u,w] \}\ in
    Function f /\ dom(f) = y /\ ran(f) = [u] × y.
Proof.
  repeat split; intros; auto.
  - appoA2H H1; appoA2H H2. deand. subst. auto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2; tauto.
    + appA2G. exists [u,z]. appoA2G; rxo.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2. deand. subst. appoA2G.
    + appA2G. PP H1 a b. deand. eins H2. exists b. appoA2G.
Qed.

Theorem MKT73 : ∀ u y, Ensemble u -> Ensemble y
  -> Ensemble ([u] × y).
Proof.
  intros. New (Ex_Lemma73 H H0). destruct H1,H2.
  rewrite <-H2 in H0. rewrite <-H3. apply AxiomV; auto.
Qed.

(* 定理74 如果x与y均为集，则 x×y 也是集 *)
Lemma Ex_Lemma74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> let f := \{\ λ u z, u ∈ x /\ z = [u] × y \}\ in
    Function f /\ dom(f) = x
    /\ ran(f) = \{ λ z, ∃ u, u ∈ x /\ z = [u] × y \}.
Proof.
  repeat split; intros; auto.
  - appoA2H H1; appoA2H H2. deand. subst. auto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2; tauto.
    + appA2G. exists ([z] × y). appoA2G; rxo. apply MKT73; eauto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2. deand. subst. appA2G.
    + appA2G. appA2H H1. rdeHex. exists x0. appoA2G.
Qed.

Lemma Lemma74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> ∪(\{ λ z, ∃ u, u ∈ x /\ z = [u] × y \}) = x × y.
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. appA2H H3. rdeHex. subst.
    PP H2 a b. deand. eins H5. subst. appoA2G.
  - PP H1 a b. deand. appA2G. exists [a] × y. split; try appoA2G.
    appA2G; rxo. apply MKT73; eauto.
Qed.

Theorem MKT74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble (x × y).
Proof.
  intros. New (Ex_Lemma74 H H0). destruct H1,H2.
  rewrite <-Lemma74,<-H3; auto. rewrite <-H2 in H.
  apply AxiomVI,AxiomV; auto.
Qed.

(* 定理75 如果f是一个函数同时f的定义域是一个集，则f是一个集 *)
Theorem MKT75 : ∀ f, Function f -> Ensemble dom(f) -> Ensemble f.
Proof.
  intros. New (MKT74 H0 (AxiomV H H0)). eapply MKT33; eauto.
  red; intros. New H2. apply H in H2 as [? []]. subst.
  appoA2G; split; [eapply Property_dom|eapply Property_ran]; eauto.
Qed.

Fact fdme : ∀ {f}, Function f -> Ensemble f -> Ensemble dom(f).
Proof.
  intros. set (g := \{\ λ u v, u ∈ f /\ v = First u \}\).
  assert (Function g).
  { unfold g; split; intros; auto.
    appoA2H H1. appoA2H H2. deand; subst; auto. }
  assert (dom(g) = f).
  { eqext.
    - appA2H H2. rdeHex. appoA2H H3; tauto.
    - appA2G. exists (First z). appA2G. rxo. New H2.
      apply H in H2 as [? []]. subst. rewrite MKT54a; ope. }
  assert (ran(g) = dom(f)).
  { eqext.
    - appA2H H3. rdeHex. appoA2H H4. deand. subst z.
      New H5. apply H in H5 as [? []]. subst x.
      rewrite MKT54a; ope. eapply Property_dom; eauto.
    - appA2H H3. rdeHex. appA2G. exists [z,x]. appoA2G.
      split; auto. rewrite MKT54a; ope; auto. }
  rewrite <-H3. rewrite <-H2 in H0. apply AxiomV; auto.
Qed.

Fact frne : ∀ {f}, Function f -> Ensemble f -> Ensemble ran(f).
Proof.
  intros. apply AxiomV; [|apply fdme]; auto. 
Qed.

(* 定义76 Exponent y x = {f:f是一个函数，f的定义域=x同时f的值域⊂ y} *)
Definition Exponent y x := \{ λ f, Function f /\ dom( f ) = x
  /\ ran( f ) ⊂ y \}.

(* 定理77 如果x与y均为集，则 Exponent y x 也是集*)
Theorem MKT77 : ∀ x y, Ensemble x -> Ensemble y
  -> Ensemble (Exponent y x).
Proof.
  intros. apply MKT33 with (x := (pow(x × y))).
  - apply MKT38a,MKT74; auto.
  - red; intros. apply MKT38b; [apply MKT74; auto|].
    red; intros. appA2H H1. deand. New H2. apply H3 in H2 as [? []].
    subst. New (Property_dom H6). New (Property_ran H6). appoA2G.
Qed.

(* 定义78 f在x上，当且仅当f为一函数同时x=f的定义域 *)
Definition On f x := Function f /\ dom(f) = x.

(* 定义79 f到y，当且仅当f是一个函数同时f的值域⊂y *)
Definition To f y := Function f /\ ran(f) ⊂ y.

(* 定义80 f到y上，当且仅当f是一个函数同时f的值域=y *)
Definition Onto f y := Function f /\ ran(f) = y.


(* 定义125 *)
Definition Restriction f x := f ∩ (x × μ).

Notation "f | ( x )" := (Restriction f x)(at level 30).

(* 定理126 *)
Theorem MKT126a : ∀ f x, Function f -> Function (f|(x)).
Proof.
  split; try red; intros; destruct H.
  - appA2H H0. destruct H2; auto.
  - appA2H H0. appA2H H1. destruct H3,H4. eapply H2; eauto.
Qed.

Theorem MKT126b : ∀ f x, Function f -> dom(f|(x)) = x ∩ dom(f).
Proof.
  intros; eqext; appA2H H0; destruct H1.
  - appA2H H1. destruct H2. appoA2H H3. destruct H4.
    apply Property_dom in H2. appA2G.
  - appA2H H2. destruct H3. appA2G; exists x0; appA2G.
    split; auto. appoA2G; split; auto. apply MKT19; ope.
Qed.

Theorem MKT126c : ∀ f x, Function f
  -> (∀ y, y ∈ dom(f|(x)) -> (f|(x))[y] = f[y]).
Proof.
  intros. apply subval; auto; [|apply MKT126a]; auto.
  red; intros. appA2H H1. tauto.
Qed.

Corollary frebig : ∀ f x, Function f -> dom(f) ⊂ x -> f|(x) = f.
Proof.
  intros; eqext.
  - appA2H H1; tauto.
  - appA2G; split; auto. New H1. apply H in H1 as [? [?]].
    subst. New H2. apply Property_dom in H2. appoA2G; split; auto.
    apply MKT19; ope.
Qed.

Corollary fresub : ∀ f h, Function f -> Function h -> h ⊂ f
  -> f|(dom(h)) = h.
Proof.
  intros; eqext.
  - appA2H H2. destruct H3. PP H4 a b. destruct H6. New H5.
    eapply subval in H5; eauto. apply Property_Fun in H3; auto.
    subst. rewrite <-H5. apply Property_Value; auto.
  - appA2G; split; auto. New H2. apply H0 in H2 as [? []]. subst.
    appoA2G. split; [eapply Property_dom; eauto|apply MKT19; ope].
Qed.

Corollary fuprv : ∀ f x y z, Ensemble x -> Ensemble y
  -> ~ x ∈ z ->  (f ∪ [[x,y]])|(z) = f|(z).
Proof.
  intros. unfold Restriction. rewrite MKT6,MKT6'.
  rewrite (MKT6' f),MKT8. apply MKT29. red; intros.
  deHin. eins H3. appoA2H H2. destruct H3. elim H1; auto.
Qed. 

