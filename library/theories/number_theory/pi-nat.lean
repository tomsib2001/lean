import data.nat data.finset .primes .prime_factorization algebra.group_bigops
open eq.ops finset -- well_founded 
decidable nat

definition is_pi_nat [reducible] (pi : nat → Prop) n := (n > 0) ∧ ∀ (p : nat), p ∈  (prime_factors n) → pi p

definition is_pi_nat1 n := (n > 0) ∧ ∀ (p : nat), p ∈  (prime_factors n) → p = 0

definition is_pi_nat_ext [reducible] pi n := (n > 0) ∧ ∀ (p : nat), p ≤ n →  p ∈  (prime_factors n) → pi p

definition is_pi_nat_ext1 n := (n > 0) ∧ ∀ (p : nat), p ≤ n →  p ∈  (prime_factors n) → p = 0


eval (3 ∈ (prime_factors 3)) -- works!!
eval (is_pi_nat_ext (λ p, p = 3) 9) -- works also

lemma is_pi_nat_ext_iff_is_pi_nat pi (n : nat) : is_pi_nat_ext pi n ↔ is_pi_nat pi n :=
iff.intro
  begin
     assume (Hext : is_pi_nat_ext pi n),
    and.intro (and.left Hext)
    (take (p : nat), 
    -- assume Hplen : p ≤ n,
    assume Hpn : p ∈ (prime_factors n),
    have Hdvdpn : p ∣ n, from dvd_of_mem_prime_factors Hpn,
    have Hlepn : p ≤ n, from (le_of_dvd (and.left Hext) Hdvdpn), 
    (and.right Hext) p Hlepn Hpn)
  end
  begin
   assume (H : is_pi_nat pi n),
   and.intro (and.left H)
    begin
      take p,
      assume Hlepn Hpn,
      (and.right H) p Hpn
    end
  end

-- probably useless since the unification algorithm already knows decidable_mem?
definition decidable_prime_factor [instance] (n p : nat) : decidable (p ∈ prime_factors n) := decidable_mem p (prime_factors n)

set_option formatter.hide_full_terms false

section utils

-- lemma zero_lt_one : (0 : nat) < (1 : nat) := (lt_succ_of_le (le.refl 0))

lemma multgt0_gt0 {m n : nat} (Hm : lt 0 m) (Hn : lt 0 n) : (lt 0 (mul m n)) := 
  have H0 : ((0 : nat) = mul (0 : nat) 0), from (nmul_zero 0),
  begin
    rewrite H0,
    apply mul_lt_mul',
    exact Hm,
    exact Hn,
    exact (nat.le_refl 0),
    exact Hm
  end
  -- mul_lt_mul'

lemma ge_prime_one (p : nat) : forall (Hprime : prime p),  le 1 p :=
  nat.cases_on p (λ H, absurd H (not_prime_zero))
  (take a H, one_le_succ a)

end utils

section partn

parameter pi : nat -> Prop
variable [Hdecpi : ∀ p, decidable (pi p)]
-- variable n : nat

include Hdecpi

check (is_true (is_pi_nat_ext pi 5))

-- definition decidable_pi [instance] (n : nat) : decidable (is_pi_nat pi n) :=
--   decidable_of_decidable_of_iff _ (is_pi_nat_ext_iff_is_pi_nat pi n)

-- some theory
set_option pp.notation false

abbreviation partp_n_pi [reducible] (n p : nat) := (if (pi p) then (p^(mult p n)) else 1)

definition partn [reducible] (n : nat) : nat := ∏ p ∈ (prime_factors n), (if (pi p) then (p^(mult p n)) else 1)

end partn

section partn_properties

parameter pi : nat -> Prop
-- variable [Hdecpi : ∀ p, decidable (pi p)]
-- variable n : nat

-- include Hdecpi


lemma ProdEmpty_gt0 {A : Type} [decidable_eq A] (f : A → nat) : (∏ p ∈ (∅ : finset A), f p) > (0 : nat) := 
  have H : (∏ p ∈ (∅ : finset A), f p) = 1, from !Prod_empty,
  begin
   rewrite H,
   exact zero_lt_one
  end

lemma Prodgt0 {A : Type} {B : A -> Prop} [decidable_eq A]  (f : A → nat) (Hfpos : ∀ n, B n → f n > 0) (s : finset A) : ∀ (HsB : ∀ n, n ∈ s → B n), (∏ p ∈ s, f p) > 0 :=
  finset.induction_on s 
 (take H, ProdEmpty_gt0 f)
 begin
   intros a s Hnmas HI HSn,
   have H1 : (Prod (insert a s) f) = f a * Prod s f, from (Prod_insert_of_not_mem f Hnmas),
   rewrite H1,
   apply multgt0_gt0,
   apply (Hfpos a),
   apply HSn,
   apply mem_insert,
   apply HI,
   intro n Hn,
   apply HSn n,
   apply mem_insert_of_mem,
   exact Hn
 end
 
lemma part_gt0 [Hdecpi : ∀ p, decidable (pi p)] (n : nat) : (partn pi n) > 0 :=
have Hpos : ∀ p, prime p →  partp_n_pi pi n p > (0 : nat), from
  (take p Hprime,
  by_cases
    (assume Hp : pi p, 
     begin
     rewrite (if_pos Hp),
     apply lt_of_succ_le,
     have H11 : (succ 0) = 1, from rfl,
     rewrite H11,
     apply pow_ge_one,
     apply ge_prime_one p Hprime, 
     end)
    (assume Hnp : ¬ pi p, 
    begin
     rewrite (if_neg Hnp),
     exact (nat.le_refl 1)
    end)),
begin
apply Prodgt0,
intro p,
apply Hpos,
intro n,
exact prime_of_mem_prime_factors
end

-- better name to find
lemma dvd_of_sub_prod {A : Type} (B : A -> Prop) [decidable_eq A]  (f g : A → nat) (Hfdivg : ∀ n, B n → f n ∣ g n )  (s : finset A) : ∀ (HsB : ∀ n, n ∈ s → B n), (∏ p ∈ s, f p) ∣ (∏ p ∈ s, g p) :=
finset.induction_on s 
begin
intro _,
apply dvd.refl
end
begin
intros a s Hnas HI HB,
have H1 : (Prod (insert a s) f) = f a * Prod s f, from (Prod_insert_of_not_mem f Hnas),
have H2 : (Prod (insert a s) g) = g a * Prod s g, from (Prod_insert_of_not_mem g Hnas),
rewrite [H1, H2],
apply mul_dvd_mul,
apply Hfdivg,
apply HB,
apply mem_insert,
apply HI,
intro n Hns,
apply HB,
apply mem_insert_of_mem,
exact Hns
end

lemma part_dvd (n : nat) (pi1 pi2 : ℕ → Prop) [Hdecpi1 : ∀ p, decidable (pi1 p)] [Hdecpi2 : ∀ p, decidable (pi2 p)] (Himp : ∀ p, pi1 p → pi2 p) :  (partn pi1 n) ∣  (partn pi2 n) :=
have Hdvd : ∀ p, prime p → partp_n_pi pi1 n p ∣ partp_n_pi pi2 n p , from
  (take p Hprime,
 by_cases
 (assume Hp : pi1 p,
 begin
 rewrite (if_pos Hp),
 rewrite (if_pos (Himp p Hp)),
 apply (dvd.refl)
end)
 (assume Hnp : ¬ pi1 p,
 begin
  rewrite (if_neg Hnp),
  apply dvd_of_eq_mul (partp_n_pi pi2 n p),
  rewrite nat.mul_comm,
  rewrite nat.mul_one
 end
)
 ),
begin
apply (dvd_of_sub_prod prime),
apply Hdvd,
intro p1,
apply prime_of_mem_prime_factors
end

-- amazing proofs!
lemma partn_0 [Hdecpi : ∀ p, decidable (pi p)] : partn pi 0 = 1 :=
begin
apply Prod_empty
end

lemma partn_1 [Hdecpi : ∀ p, decidable (pi p)] : partn pi 1 = 1 :=
begin
apply Prod_empty
end

end partn_properties

