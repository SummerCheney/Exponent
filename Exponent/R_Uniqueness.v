(** R_Uniqueness *)

Require Import R_Axioms.
Require Import R'_Axioms.

(* R'是按照和R相同的方式建立的另一个实数公理体系, 在证明唯一性相关定理时,
   R和R'相当于已有的两个条件. *)

(* 0和1的对应 *)
Theorem UniqueT1 : R <> R'
  -> (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r')
  -> f[0] = 0' /\ (ran(f) <> [0'] -> f[1] = 1')).
Admitted.

(* 整数集的对应 *)
Theorem UniqueT2 : R <> R'
  -> (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r')
  -> ran(f) <> [0'] -> (∀ m, m ∈ Z -> f[m] ∈ Z')
    /\ Function1_1 (f|(Z)) /\ dom(f|(Z)) = Z /\ ran(f|(Z)) = Z
    /\ (∀ x y, x ∈ Z -> y ∈ Z -> (x ≤ y)%r -> (f[x] ≤ f[y])%r')).
Admitted.

(* 有理数集的对应 *)
Theorem UniqueT3 : R <> R'
  -> (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ m n, m ∈ Z -> n ∈ (Z ~ [0]) -> f[(m/n)%r] = (f[m] / f[n])%r')
    /\ Function1_1 (f|(Q)) /\ dom(f|(Q)) = Q /\ ran(f|(Q)) = Q
    /\ (∀ x y, x ∈ Q -> y ∈ Q -> (x ≤ y)%r -> (f[x] ≤ f[y])%r')).
Admitted.

Theorem UniqueT4 : R <> R'
  -> (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> Function1_1 f /\ dom(f) = R /\ ran(f) = R'
    /\ (∀ x y, x ∈ R -> y ∈ R -> (x ≤ y)%r -> (f[x] ≤ f[y])%r')).
Admitted.

Theorem UniqueT5 : R <> R'
  -> ∃ f, Function1_1 f /\ dom(f) = R /\ ran(f) = R'
    /\ (∀ x y, x ∈ R -> y ∈ R
    -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r'
    /\ ((x ≤ y)%r <-> (f[x] ≤ f[y])%r')).
Admitted.




















