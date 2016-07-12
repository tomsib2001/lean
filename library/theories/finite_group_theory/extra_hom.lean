import data algebra.group data.set theories.finite_group_theory.subgroup
import theories.finite_group_theory.hom theories.finite_group_theory.subgroup
import theories.finite_group_theory.extra_subgroup
import theories.finite_group_theory.finsubg

namespace group_theory

open set group_theory group_theory.ops binary
open function

local attribute set [reducible]


section defs

variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2

-- F (as in From) is the set to which we restrict the domain
-- T (as in To) is the set to which we restrict the co-domain

-- the Prop of being hom
definition homomorphic_on [reducible] (F : set A) (f : A → B) : Prop := ∀ a b, a∈F → b ∈ F → f (a*b) = (f a)*(f b)
-- type class for inference
structure is_hom_on_class [class] (H : set A) (f : A → B) : Type :=
          (is_hom : homomorphic_on H f)
-- the proof of hom_prop if the class can be inferred
definition is_hom_on (H : set A) (f : A → B) [h : is_hom_on_class H f] : homomorphic_on H f :=
           @is_hom_on_class.is_hom A B s1 s2 H f h

definition ker_on (H : set A) (f : A → B) [h : is_hom_on_class H f] : set A := {a : A | a ∈ H ∧ f a = 1}

definition isomorphic_on (F : set A) (T : set B) (f : A → B) := inj_on f F ∧ homomorphic_on F f ∧ surj_on f F T

structure is_iso_on_class [class] (F : set A) (T : set B) (f : A → B) extends is_hom_on_class F f : Type :=
          (inj : inj_on f F) (surj : surj_on f F T)

lemma iso_on_is_inj_on (f : A → B) (F : set A) (T : set B) [h : is_iso_on_class F T f]  : inj_on f F:=
      @is_iso_on_class.inj A B s1 s2 F T f h

lemma iso_on_is_surj_on (f : A → B) (F : set A) (T : set B) [h : is_iso_on_class F T f]  : surj_on f F T:=
      @is_iso_on_class.surj A B s1 s2 F T f h

lemma iso_on_is_iso_on (f : A → B) (F : set A) (T : set B) [h : is_iso_on_class F T f] : isomorphic_on F T f:=
      and.intro (iso_on_is_inj_on f F T) (and.intro (is_hom_on F f) (iso_on_is_surj_on f F T))


end defs

section
variables {A B : Type}
variable [s1 : group A]
variables (F : set A) (T : set B)
variables [HsubgF : is_subgroup F]
include HsubgF
-- for now we don't have to suppose that B is a group

-- why do we need to do this manually? to investigate
lemma Fhasone : 1 ∈ F := @is_subgroup.has_one A s1 F HsubgF
lemma Fhasinv a (HaF : a ∈ F) : a⁻¹ ∈ F := @is_subgroup.has_inv A s1 F HsubgF a HaF
lemma Fmulclosedon (x y : A) (HxF : x ∈ F) (HyF : y ∈ F) : x * y ∈ F := @is_subgroup.mul_closed A s1 F HsubgF x y HxF HyF

definition id_is_iso_on [instance] : @is_hom_on_class A A s1 s1 F (@id A) :=
is_hom_on_class.mk (take a b ha hb, rfl)

variable [s2 : group B]
include s1
include s2

variable f : A → B

variable [h : is_hom_on_class F f]
include h

theorem hom_on_map_one : f 1 = 1 :=
        have P : f 1 = (f 1) * (f 1), from
        calc f 1 = f (1*1)  : mul_one
        ... = (f 1) * (f 1) : is_hom_on F f 1 1 (Fhasone F) (Fhasone F),
        eq.symm (mul.right_inv (f 1) ▸ (mul_inv_eq_of_eq_mul P))


theorem hom_on_map_inv (a : A) (HaF : a ∈ F) : f a⁻¹ = (f a)⁻¹ :=
        have HainvF : a⁻¹ ∈ F, from Fhasinv F a HaF ,
        have P : f 1 = 1, from hom_on_map_one F f,
        have P1 : f (a⁻¹ * a) = 1, from (eq.symm (mul.left_inv a)) ▸ P,
        have P2 : (f a⁻¹) * (f a) = 1, from (is_hom_on F f a⁻¹ a HainvF HaF) ▸ P1,
        have P3 : (f a⁻¹) * (f a) = (f a)⁻¹ * (f a), from eq.symm (mul.left_inv (f a)) ▸ P2,
        mul_right_cancel P3

theorem hom_on_map_mul_closed (H : set A) (sHF : H ⊆ F) : mul_closed_on H → mul_closed_on (f ' H) :=
        assume Pclosed, assume b1, assume b2,
        assume Pb1 : b1 ∈ f ' H, assume Pb2 : b2 ∈ f ' H,
        obtain a1 (Pa1 : a1 ∈ H ∧ f a1 = b1), from Pb1,
        obtain a2 (Pa2 : a2 ∈ H ∧ f a2 = b2), from Pb2,
        have Pa1a2 : a1 * a2 ∈ H, from Pclosed a1 a2 (and.left Pa1) (and.left Pa2),
        have Ha1F : a1 ∈ F, from mem_of_subset_of_mem sHF (and.left Pa1),
        have Ha2F : a2 ∈ F, from mem_of_subset_of_mem sHF (and.left Pa2),
        have Pb1b2 : f (a1 * a2) = b1 * b2, from calc
        f (a1 * a2) = f a1 * f a2 : is_hom_on F f a1 a2 Ha1F Ha2F
        ... = b1 * f a2 : {and.right Pa1}
        ... = b1 * b2 : {and.right Pa2},
        mem_image Pa1a2 Pb1b2

lemma ker_on.maps_to_one (x : A) (Hxker : x ∈ ker_on F f) : f x = 1 :=
  and.right Hxker

lemma ker_on.in_F (x : A) (Hxker : x ∈ ker_on F f) : x ∈ F :=
  and.left Hxker

lemma ker_on.has_one : 1 ∈ ker_on F f := and.intro (Fhasone F) (hom_on_map_one F f)

lemma ker_on.has_inv : subgroup.has_inv (ker_on F f) :=
      take a, assume Pa : a ∈ F ∧ f a = 1,
      and.intro
      (Fhasinv F a (and.left Pa))
      (calc
      f a⁻¹ = (f a)⁻¹ : by rewrite (hom_on_map_inv F f a (and.left Pa))
      ... = 1⁻¹ : by rewrite (and.right Pa)
      ... = 1 : by rewrite one_inv)

lemma ker_on.mul_closed : mul_closed_on (ker_on F f) :=
      take x y, assume (Px : x ∈ F ∧ f x = 1) (Py : y ∈ F ∧ f y = 1), and.intro
      (Fmulclosedon F x y (and.left Px) (and.left Py))
      (calc
      f (x*y) = (f x) * (f y) : by rewrite [is_hom_on F f x y (and.left Px) (and.left Py)
      ]
      ... = 1 : by rewrite [and.right Px, and.right Py, mul_one])

-- definition same_left_right_coset_on (N : set A) := ∀ x, x ∈ F → x ∘> N = N <∘ x

-- this one is feasible but technical, skip for now
lemma ker_on.normal : same_left_right_coset_on F (ker_on F f) :=
      take a Ha , funext (assume x, begin
      esimp [ker_on, set_of, glcoset, grcoset],
      apply sorry
      -- rewrite (is_hom_on F f a 1 Ha (Fhasone F)),
      -- rewrite [*(is_hom_on F f), mul_eq_one_iff_mul_eq_one (f a⁻¹) (f x)]
      end)

definition ker_on_is_normal_subgroup : is_normal_subgroup_of F (ker_on F f) :=
  is_normal_subgroup_of.mk (ker_on.has_one F f) (ker_on.mul_closed F f) (ker_on.has_inv F f) (ker_on.normal F f)

-- additional subgroup variable
variable {H : set A}
variable [is_subgH : is_subgroup H]
include is_subgH

theorem hom_on_map_subgroup (sHF : H ⊆ F) : is_subgroup (f ' H) :=
  have Pone : 1 ∈ f ' H, from mem_image (@subg_has_one _ _ H _) (hom_on_map_one F f),
  have Pclosed : mul_closed_on (f ' H), from hom_on_map_mul_closed F f H sHF subg_mul_closed,
  have Pinv : ∀ b, b ∈ f ' H → b⁻¹ ∈ f ' H, from
  assume b, assume Pimg,
  obtain a (Pa : a ∈ H ∧ f a = b), from Pimg,
  have HaF : a ∈ F, from mem_of_subset_of_mem sHF (and.left Pa),
  have Painv : a⁻¹ ∈ H, from subg_has_inv a (and.left Pa),
  have Pfainv : (f a)⁻¹ ∈ f ' H, from mem_image Painv (hom_on_map_inv F f a HaF),
    and.right Pa ▸ Pfainv,
  is_subgroup.mk Pone Pclosed Pinv

lemma antecedents_ker (x y : A) : f x = f y → ∃ h, h ∈ ker_on F f ∧ x = h * y := sorry

print inv_image

-- variable [deceqA : decidable_eq A]
-- variable {Hf : finset A}
-- variable [is_finsubgHf : is_finsubg Hf]
-- include is_finsubgHf

-- theorem hom_on_map_subgroup (sHF : H ⊆ F) : is_finsubg (f ' H) :=

end


-- section hom_theorem

-- variables {A B : Type}
-- variable [s1 : group A]
-- variable [s2 : group B]
-- include s1
-- include s2

-- variable {f : A → B}

-- variables (F : set A) -- (T : set B)
-- variables [HsubgF : is_subgroup F]
-- include HsubgF


-- variable [h : is_hom_on_class F f]
-- include h

-- definition ker_on__nsubg [instance] : is_normal_subgroup_of F (ker_on F f) :=
--            is_normal_subgroup_of.mk (ker_on.has_one F f) (ker_on.mul_closed F f)
--            (ker_on.has_inv F f) (ker_on.normal F f)




-- PATCHED UNTIL HERE
-- PATCHED UNTIL HERE
-- PATCHED UNTIL HERE
-- PATCHED UNTIL HERE
-- PATCHED UNTIL HERE
-- PATCHED UNTIL HERE



-- definition quot_over_ker_on [instance] : group (coset_of (ker_on F f)) := mk_quotient_group (ker_on F f)
-- -- under the wrap the tower of concepts collapse to a simple condition
-- example (a x : A) : (x ∈ a ∘> ker f) = (f (a⁻¹*x) = 1) := rfl
-- lemma ker_coset_same_val (a b : A): same_lcoset (ker f) a b → f a = f b :=
--       assume Psame,
--       have Pin : f (b⁻¹*a) = 1, from subg_same_lcoset_in_lcoset a b Psame,
--       have P : (f b)⁻¹ * (f a) = 1, from calc
--       (f b)⁻¹ * (f a) = (f b⁻¹) * (f a) :  (hom_map_inv f)
--       ... = f (b⁻¹*a) : by rewrite [is_hom f]
--       ... = 1 : by rewrite Pin,
--       eq.symm (inv_inv (f b) ▸ inv_eq_of_mul_eq_one P)

-- definition ker_natural_map : (coset_of (ker f)) → B :=
--            quot.lift f ker_coset_same_val

-- example (a : A) : ker_natural_map ⟦a⟧ = f a := rfl
-- lemma ker_coset_hom (a b : A) :
--       ker_natural_map (⟦a⟧*⟦b⟧) = (ker_natural_map ⟦a⟧) * (ker_natural_map ⟦b⟧) := calc
--       ker_natural_map (⟦a⟧*⟦b⟧) = ker_natural_map ⟦a*b⟧ : rfl
--       ... = f (a*b) : rfl
--       ... = (f a) * (f b) : by rewrite [is_hom f]
--       ... = (ker_natural_map ⟦a⟧) * (ker_natural_map ⟦b⟧) : rfl

-- lemma ker_map_is_hom : homomorphic (ker_natural_map : coset_of (ker f) → B) :=
--   take aK bK,
--       quot.ind (λ a, quot.ind (λ b, ker_coset_hom a b) bK) aK

-- lemma ker_coset_inj (a b : A) : (ker_natural_map ⟦a⟧ = ker_natural_map ⟦b⟧) → ⟦a⟧ = ⟦b⟧ :=
--       assume Pfeq : f a = f b,
--       have Painb : a ∈ b ∘> ker f, from calc
--       f (b⁻¹*a) = (f b⁻¹) * (f a) : by rewrite [is_hom f]
--       ... = (f b)⁻¹ * (f a)       : by rewrite (hom_map_inv f)
--       ... = (f a)⁻¹ * (f a)       : by rewrite Pfeq
--       ... = 1                     : by rewrite (mul.left_inv (f a)),
--       quot.sound (@subg_in_lcoset_same_lcoset _ _ (ker f) _ a b Painb)

-- lemma ker_map_is_inj : injective (ker_natural_map : coset_of (ker f) → B) :=
--       take aK bK,
--       quot.ind (λ a, quot.ind (λ b, ker_coset_inj a b) bK) aK

-- -- a special case of the fundamental homomorphism theorem or the first isomorphism theorem
-- theorem first_isomorphism_theorem : isomorphic (ker_natural_map : coset_of (ker f) → B) :=
--         and.intro ker_map_is_inj ker_map_is_hom

-- end hom_theorem



end group_theory
