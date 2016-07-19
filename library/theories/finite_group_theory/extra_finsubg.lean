import data algebra.group theories.finite_group_theory.subgroup theories.finite_group_theory.finsubg data.finset.extra_finset
open function finset group_theory subtype nat

open group_theory nat finset

section missing

lemma injective_image {A B : Type} [HdeceqB : decidable_eq B] (f : A → B) (Hinjf : injective f) : injective (image f : finset A → finset B) :=
  assume s1 s2 Heqfs1s2,
  eq_of_subset_of_subset
  (subset_of_forall
    (take x Hxs1,
    have Hfx : f x ∈ f ' s2, from eq.subst Heqfs1s2 (mem_image_of_mem f Hxs1),
    obtain x2 (Hx2 : x2 ∈ s2 ∧ f x2 = f x), from eq.subst (mem_image_eq f) Hfx,
    have Heq : x2 = x, from Hinjf (and.right Hx2),
    eq.subst Heq (and.left Hx2)
    ))
  (subset_of_forall
  (
  take x Hxs2,
    have Hfx : f x ∈ f ' s1, from eq.substr Heqfs1s2 (mem_image_of_mem f Hxs2),
    obtain x1 (Hx1 : x1 ∈ s1 ∧ f x1 = f x), from eq.subst (mem_image_eq f) Hfx,
    have Heq : x1 = x, from Hinjf (and.right Hx1),
    eq.subst Heq (and.left Hx1)
  ))

end missing


namespace group_theory

section fin_rcoset

variables {A : Type} [HdeceqA : decidable_eq A] [groupA : group A]
variables (H G : finset A)
variable [is_finsubgG : is_finsubg G]
variable [is_finsubgH : is_finsubg H]
include HdeceqA
include groupA

local attribute fin_lcosets [reducible]

definition fin_rcosets [reducible] : finset (finset A) :=  (fin_rcoset H) ' G

include is_finsubgG
include is_finsubgH

lemma image_inv : inv ' G = G :=
  ext (take x, iff.intro (assume HxinvG,
  begin
   rewrite mem_image_iff at HxinvG,
   cases HxinvG with y Hy,
   cases Hy with HyG Hyinv,
   rewrite -Hyinv,
   apply finsubg_has_inv G HyG,
  end) (assume HxG, mem_image (finsubg_has_inv G HxG) (inv_inv x)))

lemma image_fin_inv_lcosets : fin_inv ' (fin_lcosets H G) = fin_rcosets H G :=
  begin
   rewrite -image_comp,
   rewrite ↑fin_rcosets,
   rewrite -(image_inv G G) at {2},
   rewrite -image_comp,
   congruence,
   apply funext, intro x,
   rewrite ↑comp,
   rewrite (finsubg_inv_lcoset_eq_rcoset)
  end

lemma injective_fin_inv : @injective (finset A) _ fin_inv := injective_image inv (take a b, inv.inj)

lemma inj_on_fin_inv (B : finset (finset A)) : set.inj_on fin_inv B :=
  take a b Ha Hb Heq, injective_fin_inv H G Heq

lemma card_rcosets_eq_card_lcosets :
  card (fin_rcosets H G) = card (fin_lcosets H G) :=
  begin
   have fin_rcosets H G = fin_inv ' (fin_lcosets H G), from eq.symm !image_fin_inv_lcosets,
  rewrite this,
  rewrite (card_image_eq_of_inj_on (inj_on_fin_inv H G _)),
  end

--   calc
--   card (fin_rcosets H G) = card (fin_inv ' (fin_lcosets H G)) : {image_fin_inv_lcosets H G}
--   ...                    = card (fin_lcosets H G) : sorry
--   -- begin
--   --   rewrite -(image_fin_inv_lcosets H G),
--   -- -- card_image_eq_of_inj_on _
--   -- end
-- end

end fin_rcoset

section groupStructure

definition is_finsubg_prop [class] (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] (A : finset G) : Prop :=
  1 ∈ A ∧ finset_mul_closed_on A ∧ finset_has_inv A

attribute is_finsubg_prop [reducible]

definition is_finsubg_is_finsubg_prop {G : Type} [ambientG : group G]
[deceqG : decidable_eq G] {A : finset G} : is_finsubg_prop G A → is_finsubg A :=
  assume H,
  is_finsubg.mk (and.left H) (and.left (and.right H)) (and.right (and.right H))

definition is_finsubg_prop_is_finsubg {G : Type} [ambientG : group G]
[deceqG : decidable_eq G] {A : finset G} (Hfinsubg : is_finsubg A) : is_finsubg_prop G A :=
is_finsubg.destruct Hfinsubg (take H1 Hmulclosed Hhasinv, and.intro H1 (and.intro Hmulclosed Hhasinv))

structure Fin_subg (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] := (carrier : finset G) (struct : is_finsubg_prop G carrier)

attribute Fin_subg.carrier [coercion] [reducible]
attribute Fin_subg.struct [instance] [reducible]

lemma struct_irrelevant (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] (H : finset G) (fsg1 : is_finsubg_prop G H) (fsg2 : is_finsubg_prop G H) :
  fsg1 = fsg2 := rfl

lemma injective_projection (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] -- (H1 H2 : Fin_subg G)
:
  function.injective (@Fin_subg.carrier G ambientG deceqG) :=
  take (H2 : Fin_subg G) (H1 : Fin_subg G),
  Fin_subg.rec_on H1 (Fin_subg.rec_on H2
  (take c1 p1 c2 p2 Heq,
  begin
   have Heqc : c1 = c2, from Heq,
   clear Heq,
   revert p1,
   rewrite Heqc,
   intro p1,
   reflexivity
  end
  ))

lemma finSubGroups [instance] (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] : fintype (Fin_subg G) := sorry

example : ∀ (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] , decidable (∀ (H : Fin_subg G), 1 ∈ H) :=
take G aG decG,
  decidable_forall_finite

definition subgroup (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] := { S : finset G | is_finsubg_prop G S }

definition is_fin_subg_in_all_subgroups [instance] {G : Type} [ambientG : group G]
[deceqG : decidable_eq G] (S : subgroup G) : is_finsubg (elt_of S) :=
  is_finsubg_is_finsubg_prop (has_property S)

end groupStructure


-- some theory to categorize more precisely later




variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

section extra_lcoset_type

variable H : finset G
variable {H}

-- we can't make this an instance otherwise we would have a loop, because the opposite can also be deduced
definition is_finsubg_subg [subgH : is_subgroup (ts H)] : is_finsubg H :=
  have has1H : 1 ∈ H, from (@subg_has_one G _ H subgH),
  have fmcH : finset_mul_closed_on H, from take x y Hx Hy,
  begin apply (@subg_mul_closed G _ H _ x y Hx Hy) end,
  have invH : finset_has_inv H, from @subg_has_inv G _ H _,
  is_finsubg.mk has1H fmcH invH

variable [finsubgH : is_finsubg H]
include finsubgH

-- variable (H)

variable L : finset G
variable [HsKNH : L ⊆ normalizer H]
variable [sgL : is_finsubg L]
include sgL
include HsKNH
open eq.ops

variable {L}

lemma lcoset_subset_normalizer_of_mem_gen {g : G} :
  g ∈ L → fin_lcoset H g ⊆ normalizer H :=
assume Pgin,
have HgH: g ∈ normalizer H, from mem_of_subset_of_mem HsKNH Pgin,
fin_lcoset_subset subset_normalizer g HgH

-- set_option unifier.max_steps 1000000

-- lemma lrcoset_same_of_mem_normalizer_gen {g : G} :
--   g ∈ L → fin_lcoset H g = fin_rcoset H g :=
-- assume Pg,
-- have HgH: g ∈ normalizer H, from mem_of_subset_of_mem HsKNH Pg,
-- ext take h, iff.intro
--   (assume Pl, obtain j Pjin Pj, from exists_of_mem_image Pl,
--   mem_image (of_mem_sep HgH j Pjin)
--   (calc g*j*g⁻¹*g = g*j : inv_mul_cancel_right
--                 ... = h   : Pj))
--   (assume Pr, obtain j Pjin Pj, from exists_of_mem_image Pr,
--   mem_image (of_mem_sep (finsubg_has_inv (normalizer H) HgH) j Pjin)
--   (calc g*(g⁻¹*j*g⁻¹⁻¹) = g*(g⁻¹*j*g)   : inv_inv
--                    ... = g*(g⁻¹*(j*g)) : mul.assoc
--                    ... = j*g           : mul_inv_cancel_left
--                    ... = h             : Pj))


lemma lcoset_mul_eq_lcoset_gen (J K : lcoset_type L H) {g : G} :
  g ∈ elt_of J → (lcoset_mul J K) = fin_lcoset (elt_of K) g :=
assume Pgin,
obtain j Pjin Pj, from has_property J,
have HjNH : j ∈ normalizer H, from mem_of_subset_of_mem HsKNH Pjin,
obtain k Pkin Pk, from has_property K,
have HkNH : k ∈ normalizer H, from mem_of_subset_of_mem HsKNH Pkin,
Union_const (lcoset_not_empty J) begin
  rewrite [-Pk], intro h Phin,
  have Phinn : h ∈ normalizer H,
    begin
      apply mem_of_subset_of_mem (lcoset_subset_normalizer_of_mem_gen HjNH),
      rewrite Pj, assumption
    end,
  revert Phin Pgin,
  rewrite [-Pj, *fin_lcoset_same],
  intro Pheq Pgeq,
  rewrite [*(lrcoset_same_of_mem_normalizer HkNH), *fin_lrcoset_comm, Pheq, Pgeq]
end

check lcoset_mul_eq_lcoset_gen
check lcoset_mul_eq_lcoset
check lcoset_mul

-- set_option pp.implicit true

-- lemma lcoset_mul_is_lcoset_gen (J K : lcoset_type L H) :
--   is_fin_lcoset L H (lcoset_mul J K) :=
-- obtain j (Pjin : j ∈ L) Pj, from has_property J,
-- -- have HjNH : j ∈ normalizer H, from mem_of_subset_of_mem HsKNH Pjin,
-- obtain k (Pkin : k ∈ L) Pk, from has_property K,
-- -- have HkNH : k ∈ normalizer H, from mem_of_subset_of_mem HsKNH Pkin,
-- exists.intro (j*k) (and.intro (finsubg_mul_closed L Pjin Pkin)
-- begin rewrite [lcoset_mul_eq_lcoset_gen J K (Pj ▸ fin_mem_lcoset j), -fin_lcoset_compose, Pk] end
--   )


-- definition fin_coset_mul_gen (J K : lcoset_type L H) : lcoset_type L H :=
-- tag (lcoset_mul J K) (lcoset_mul_is_lcoset J K)

definition fin_coset_group_gen [instance] : group (lcoset_type L H) := sorry
-- group.mk fin_coset_mul fin_coset_mul_assoc fin_coset_one fin_coset_one_mul fin_coset_mul_one fin_coset_inv fin_coset_left_inv


-- definition fin_coset_subgroup [instance] : group (lcoset_type K H) :=
-- group.mk fin_coset_mul fin_coset_mul_assoc fin_coset_one fin_coset_one_mul fin_coset_mul_one fin_coset_inv fin_coset_left_inv

end extra_lcoset_type


lemma subset_one_group (A : finset G) (hA : is_finsubg A) : subset '{(1:G)} A :=
begin
  rewrite subset_eq_to_set_subset,
  intro x,
  rewrite to_set_insert,
  rewrite to_set_empty,
  intro Hx,
  have H1 : x = 1,
  from eq_of_mem_singleton Hx,
  rewrite H1,
  exact finsubg_has_one A
  end

lemma card1 : card ('{(1:G)}) = 1 :=
  calc
  card ('{(1:G)}) = card (empty) + 1 : card_insert_of_not_mem (!not_mem_empty)
  ...             = 0 + 1 : {card_empty}
  ...             = 1 : nat.add_zero

lemma lmul_one_id (x : G) : lmul_by x 1 = x :=
calc
  lmul_by x 1 = (λ y, x * y) 1 : rfl
  ...         = (x * 1)        : rfl
  ...         = x              : !mul_one


local attribute finset_has_inv [reducible]

lemma decidable_is_finsubg_prop [instance] {A : finset G} : decidable (is_finsubg_prop G A) := _

lemma lagrange_div {H1 H2 : finset G} [H1gr : is_finsubg H1] [ H2gr : is_finsubg H2]
  (HS : subset H1 H2) :
  card H1 ∣ card H2 :=
  dvd_of_eq_mul _ _ _ (eq.subst !nat.mul_comm (lagrange_theorem HS))

-- the index of the subgroup A inside the group B
-- is it better to have index A B or index B A?
-- here index A B = [B : A] (and thus A is a subset of B)
definition index [reducible] (A B : finset G) -- (Psub : finset.subset A B)
:= finset.card (fin_lcosets A B)

lemma index_card_fin_coset_type (A B : finset G) [is_finsubg B] : index A B = fintype.card (lcoset_type B A) :=
  begin
  rewrite card_lcoset_type
  end

lemma index_card_div (A B : finset G) [HA : is_finsubg A] [HB : is_finsubg B] (Psub : A ⊆ B) :
  card B = (index A B) * (card A) :=
calc
  card B = card (fin_lcosets A B) * card A : lagrange_theorem Psub
  ...    = (index A B) * (card A) : rfl

-- it would be nice if this were cheap...
lemma index_one (B : finset G)  : index '{(1:G)} B = finset.card B :=
  calc
  index '{(1:G)} B = finset.card (fin_lcosets '{(1:G)}  B) : rfl
  ...              = finset.card (image (fin_lcoset '{(1:G)}) B) : rfl
-- problem here : fin_lcoset '{(1:G)} has type G → finset G instead of
-- B → finset G
  ...              = finset.card B : sorry --(card_eq_card_image_of_inj (inj_fin_lcoset_one))
  ...              = _ : sorry


-- some theory of generated subgroup

-- we cannot define this properly because Intersection is not in the library yet
-- definition generated (A : finset G) := sInter { S : finset.powerset G | is_finsubg_prop S}
-- finset.set_
-- lemma is_min_generated (A H : finset G) [HgrH : is_finsubg H] :
--   minSet (is_finsubg_prop G) H := sorry

end group_theory
