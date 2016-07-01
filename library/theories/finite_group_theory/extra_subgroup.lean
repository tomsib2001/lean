import data algebra.group data theories.finite_group_theory.subgroup
open function eq.ops

open set

namespace group_theory
  namespace ops
    infixr `∘>`:55 := glcoset -- stronger than = (50), weaker than * (70)
    infixl `<∘`:55 := grcoset
    infixr `∘c`:55 := conj_by
  end ops
end group_theory

open group_theory.ops
section
variable {A : Type}
variable [s : group A]
include s
-- variable (F : set A)
-- variable [subgF : is_subgroup F]
-- include subgF


-- definition in_lcoset_of [reducible] H (a b : A) := a ∈ b ∘> H
-- definition in_rcoset_of [reducible] H (a b : A) := a ∈ H <∘ b
-- definition same_lcoset_of [reducible] H (a b : A) := a ∘> H = b ∘> H
-- definition same_rcoset_of [reducible] H (a b : A) := H <∘ a = H <∘ b


definition same_left_right_coset_on (F : set A) (N : set A) :=
  ∀ x, x ∈ F → x ∘> N = N <∘ x
-- structure is_subgroup [class] (H : set A) : Type :=
--   (has_one : H 1)
--   (mul_closed : mul_closed_on H)
--   (has_inv : subgroup.has_inv H)

structure is_normal_subgroup_of [class] (F : set A) [subgF : is_subgroup F] (N : set A) extends is_subgroup N :=
  (normal : same_left_right_coset_on F N)


end













section subgroup
-- variable {A : Type}
-- variable [s : group A]
-- include s
-- variable {H : set A}
-- variable [is_subg : is_subgroup H]
-- include is_subg
-- section set_reducible
-- local attribute set [reducible]
-- lemma subg_has_one : H (1 : A) := @is_subgroup.has_one A s H is_subg
-- lemma subg_mul_closed : mul_closed_on H := @is_subgroup.mul_closed A s H is_subg
-- lemma subg_has_inv : subgroup.has_inv H := @is_subgroup.has_inv A s H is_subg
-- lemma subgroup_coset_id : ∀ a, a ∈ H → (a ∘> H = H ∧ H <∘ a = H) :=
--       take a, assume PHa : H a,
--       have Pl : a ∘> H ⊆ H, from closed_lcontract a H subg_mul_closed PHa,
--       have Pr : H <∘ a ⊆ H, from closed_rcontract a H subg_mul_closed PHa,
--       have PHainv : H a⁻¹, from subg_has_inv a PHa,
--       and.intro
--       (ext (assume x,
--         begin
--           esimp [glcoset, mem],
--           apply iff.intro,
--             apply Pl,
--             intro PHx, exact (subg_mul_closed a⁻¹ x PHainv PHx)
--         end))
--       (ext (assume x,
--         begin
--           esimp [grcoset, mem],
--           apply iff.intro,
--             apply Pr,
--             intro PHx, exact (subg_mul_closed x a⁻¹ PHx PHainv)
--         end))
-- lemma subgroup_lcoset_id : ∀ a, a ∈ H → a ∘> H = H :=
--       take a, assume PHa : H a,
--       and.left (subgroup_coset_id a PHa)
-- lemma subgroup_rcoset_id : ∀ a, a ∈ H → H <∘ a = H :=
--       take a, assume PHa : H a,
--       and.right (subgroup_coset_id a PHa)
-- lemma subg_in_coset_refl (a : A) : a ∈ a ∘> H ∧ a ∈ H <∘ a :=
--       have PH1 : H 1, from subg_has_one,
--       have PHinvaa : H (a⁻¹*a), from (eq.symm (mul.left_inv a)) ▸ PH1,
--       have PHainva : H (a*a⁻¹), from (eq.symm (mul.right_inv a)) ▸ PH1,
--       and.intro PHinvaa PHainva
-- end set_reducible
-- lemma subg_in_lcoset_same_lcoset (a b : A) : in_lcoset H a b → same_lcoset H a b :=
--       assume Pa_in_b : H (b⁻¹*a),
--       have Pbinva : b⁻¹*a ∘> H = H, from subgroup_lcoset_id (b⁻¹*a) Pa_in_b,
--       have Pb_binva : b ∘> b⁻¹*a ∘> H = b ∘> H, from Pbinva ▸ rfl,
--       have Pbbinva : b*(b⁻¹*a)∘>H = b∘>H, from glcoset_compose b (b⁻¹*a) H ▸ Pb_binva,
--       mul_inv_cancel_left b a ▸ Pbbinva
-- lemma subg_same_lcoset_in_lcoset (a b : A) : same_lcoset H a b → in_lcoset H a b :=
--       assume Psame : a∘>H = b∘>H,
--       have Pa : a ∈ a∘>H, from and.left (subg_in_coset_refl a),
--       by exact (Psame ▸ Pa)
-- lemma subg_lcoset_same (a b : A) : in_lcoset H a b = (a∘>H = b∘>H) :=
--       propext(iff.intro (subg_in_lcoset_same_lcoset a b) (subg_same_lcoset_in_lcoset a b))
-- lemma subg_rcoset_same (a b : A) : in_rcoset H a b = (H<∘a = H<∘b) :=
--       propext(iff.intro
--       (assume Pa_in_b : H (a*b⁻¹),
--       have Pabinv : H<∘a*b⁻¹ = H, from subgroup_rcoset_id (a*b⁻¹) Pa_in_b,
--       have Pabinv_b : H <∘ a*b⁻¹ <∘ b = H <∘ b, from Pabinv ▸ rfl,
--       have Pabinvb : H <∘ a*b⁻¹*b = H <∘ b, from grcoset_compose (a*b⁻¹) b H ▸ Pabinv_b,
--       inv_mul_cancel_right a b ▸ Pabinvb)
--       (assume Psame,
--       have Pa : a ∈ H<∘a, from and.right (subg_in_coset_refl a),
--       by exact (Psame ▸ Pa)))
-- lemma subg_same_lcoset.refl (a : A) : same_lcoset H a a := rfl
-- lemma subg_same_rcoset.refl (a : A) : same_rcoset H a a := rfl
-- lemma subg_same_lcoset.symm (a b : A) : same_lcoset H a b → same_lcoset H b a := eq.symm
-- lemma subg_same_rcoset.symm (a b : A) : same_rcoset H a b → same_rcoset H b a := eq.symm
-- lemma subg_same_lcoset.trans (a b c : A) : same_lcoset H a b → same_lcoset H b c → same_lcoset H a c :=
--       eq.trans
-- lemma subg_same_rcoset.trans (a b c : A) : same_rcoset H a b → same_rcoset H b c → same_rcoset H a c :=
--       eq.trans
-- variable {S : set A}
-- lemma subg_lcoset_subset_subg (Psub : S ⊆ H) (a : A) : a ∈ H → a ∘> S ⊆ H :=
--       assume Pin, have P : a ∘> S ⊆ a ∘> H, from glcoset_sub a S H Psub,
--       subgroup_lcoset_id a Pin ▸ P
end subgroup




















section normal_subg
open quot
variable {A : Type}
variable [s : group A]
include s
variable (N : set A)
variable (F : set A)
variable [subgF : is_subgroup F]
include subgF

-- N is a normal subgroup of F
variable [is_nsubg : is_normal_subgroup_of F N]

include is_nsubg

local notation a `~` b := same_lcoset N a b -- note : does not bind as strong as →

lemma nsubg_normal_F : same_left_right_coset_on F N := @is_normal_subgroup_of.normal A s F subgF N is_nsubg

lemma nsubg_same_lcoset_product_F : ∀ a1 a2 b1 b2, a1 ∈ F → a2 ∈ F → b1 ∈ F → b2 ∈ F → (a1 ~ b1) → (a2 ~ b2) →  ((a1*a2) ~ (b1*b2)) :=
  take a1 a2 b1 b2 Ha1 Ha2 Hb1 Hb2,
  assume Psame1 : a1 ∘> N = b1 ∘> N,
  assume Psame2 : a2 ∘> N = b2 ∘> N,
  have Hb1b2 : b1 * b2 ∈ F, from begin apply subg_mul_closed, exact Hb1, exact Hb2 end,
  calc
  a1*a2 ∘> N = a1 ∘> a2 ∘> N : glcoset_compose
  ... = a1 ∘> b2 ∘> N :    by rewrite Psame2
  ... = a1 ∘> (N <∘ b2) :  by rewrite (nsubg_normal_F N F b2 Hb2)
  ... = (a1 ∘> N) <∘ b2 :  by rewrite lcoset_rcoset_assoc
  ... = (b1 ∘> N) <∘ b2 :  by rewrite Psame1
  ... = N <∘ b1 <∘ b2 :    by rewrite (nsubg_normal_F N F b1 Hb1)
  ... = N <∘ (b1*b2) :     by rewrite grcoset_compose
  ... = (b1*b2) ∘> N :     by rewrite (nsubg_normal_F N F (b1*b2) Hb1b2)

example (a b : A) : (a⁻¹ ~ b⁻¹) = (a⁻¹ ∘> N = b⁻¹ ∘> N) := rfl
lemma nsubg_same_lcoset_inv_F : ∀ a b, a ∈ F → b ∈ F → (a ~ b) → (a⁻¹ ~ b⁻¹) :=
  take a b Ha Hb, assume Psame : a ∘> N = b ∘> N,
  have Hbinv : b⁻¹ ∈ F, from begin apply subg_has_inv, exact Hb end,
  calc
  a⁻¹ ∘> N = a⁻¹*b*b⁻¹ ∘> N    : by rewrite mul_inv_cancel_right
  ... = a⁻¹*b ∘> b⁻¹ ∘> N      : by rewrite glcoset_compose
  ... = a⁻¹*b ∘> (N <∘ b⁻¹)    : by rewrite (nsubg_normal_F N F (b⁻¹) Hbinv)
  ... = (a⁻¹*b ∘> N) <∘ b⁻¹    : by rewrite lcoset_rcoset_assoc
  ... = (a⁻¹ ∘> b ∘> N) <∘ b⁻¹ : by rewrite glcoset_compose
  ... = (a⁻¹ ∘> a ∘> N) <∘ b⁻¹ : by rewrite Psame
  ... = N <∘ b⁻¹               : by rewrite glcoset_inv
  ... = b⁻¹ ∘> N               : by rewrite (nsubg_normal_F N F (b⁻¹) Hbinv)

definition nsubg_setoid_F [instance] : setoid A :=
  setoid.mk (same_lcoset N)
  (mk_equivalence (same_lcoset N) (subg_same_lcoset.refl) (subg_same_lcoset.symm) (subg_same_lcoset.trans))

definition coset_of_onF : Type := quot (nsubg_setoid_F N F)

-- check coset_of_onF

-- definition coset_inv_base (a : A) : coset_of N := ⟦a⁻¹⟧
-- definition coset_product (a b : A) : coset_of N := ⟦a*b⟧
-- lemma coset_product_well_defined : ∀ a1 a2 b1 b2, (a1 ~ b1) → (a2 ~ b2) → ⟦a1*a2⟧ = ⟦b1*b2⟧ :=
--       take a1 a2 b1 b2, assume P1 P2,
--       quot.sound (nsubg_same_lcoset_product N a1 a2 b1 b2 P1 P2)
-- definition coset_mul (aN bN : coset_of N) : coset_of N :=
--   quot.lift_on₂ aN bN (coset_product N) (coset_product_well_defined N)
-- lemma coset_inv_well_defined : ∀ a b, (a ~ b) → ⟦a⁻¹⟧ = ⟦b⁻¹⟧ :=
--       take a b, assume P, quot.sound (nsubg_same_lcoset_inv N a b P)
-- definition coset_inv (aN : coset_of N) : coset_of N :=
--            quot.lift_on aN (coset_inv_base N) (coset_inv_well_defined N)
-- definition coset_one :  coset_of N := ⟦1⟧

-- local infixl `cx`:70 := coset_mul N
-- example (a b c : A) : ⟦a⟧ cx ⟦b*c⟧ = ⟦a*(b*c)⟧ := rfl

-- lemma coset_product_assoc (a b c : A) : ⟦a⟧ cx ⟦b⟧ cx ⟦c⟧ = ⟦a⟧ cx (⟦b⟧ cx ⟦c⟧) := calc
--       ⟦a*b*c⟧ = ⟦a*(b*c)⟧ : {mul.assoc a b c}
--       ... = ⟦a⟧ cx ⟦b*c⟧ : rfl
-- lemma coset_product_left_id (a : A) : ⟦1⟧ cx ⟦a⟧ = ⟦a⟧ := calc
--       ⟦1*a⟧ = ⟦a⟧ : {one_mul a}
-- lemma coset_product_right_id (a : A) : ⟦a⟧ cx ⟦1⟧ = ⟦a⟧ := calc
--       ⟦a*1⟧ = ⟦a⟧ : {mul_one a}
-- lemma coset_product_left_inv (a : A) : ⟦a⁻¹⟧ cx ⟦a⟧ = ⟦1⟧ := calc
--       ⟦a⁻¹*a⟧ = ⟦1⟧ : {mul.left_inv a}
-- lemma coset_mul.assoc (aN bN cN : coset_of N) : aN cx bN cx cN = aN cx (bN cx cN) :=
--       quot.ind (λ a, quot.ind (λ b, quot.ind (λ c, coset_product_assoc N a b c) cN) bN) aN
-- lemma coset_mul.one_mul (aN : coset_of N) : coset_one N cx aN = aN :=
--       quot.ind (coset_product_left_id N) aN
-- lemma coset_mul.mul_one (aN : coset_of N) : aN cx (coset_one N) = aN :=
--       quot.ind (coset_product_right_id N) aN
-- lemma coset_mul.left_inv (aN : coset_of N) : (coset_inv N aN) cx aN = (coset_one N) :=
--       quot.ind (coset_product_left_inv N) aN
-- definition mk_quotient_group : group (coset_of N):=
--            group.mk (coset_mul N) (coset_mul.assoc N) (coset_one N)  (coset_mul.one_mul N) (coset_mul.mul_one N) (coset_inv N) (coset_mul.left_inv N)

end normal_subg

-- namespace group_theory
-- namespace quotient
-- section
-- open quot
-- variable {A : Type}
-- variable [s : group A]
-- include s
-- variable {N : set A}
-- variable [is_nsubg : is_normal_subgroup N]
-- include is_nsubg
-- definition quotient_group [instance] : group (coset_of N) := mk_quotient_group N

-- example (aN : coset_of N) : aN * aN⁻¹ = 1 := mul.right_inv aN
-- definition natural (a : A) : coset_of N := ⟦a⟧

-- end
-- end quotient
-- end group_theory



-- namespace group_theory
-- namespace quotient
-- section
-- open quot
-- variable {A : Type}
-- variable [s : group A]
-- include s
-- variable {N : set A}
-- variable [is_nsubg : is_normal_subgroup N]
-- include is_nsubg
-- definition quotient_group [instance] : group (coset_of N) := mk_quotient_group N

-- example (aN : coset_of N) : aN * aN⁻¹ = 1 := mul.right_inv aN
-- definition natural (a : A) : coset_of N := ⟦a⟧

-- end
-- end quotient
-- end group_theory
