import data algebra.group .subgroup .finsubg data.finset.extra_finset
open function finset group_theory subtype nat set

namespace group_theory

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
definition index [reducible] (A B : finset G) -- (Psub : finset.subset A B)
:= finset.card (fin_lcosets A B)

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
definition generated (A : finset G) := sInter { S : finset.powerset G | is_finsubg_prop S} 
finset.set_
-- lemma is_min_generated (A H : finset G) [HgrH : is_finsubg H] : 
--   minSet (is_finsubg_prop G) H := sorry

end group_theory
