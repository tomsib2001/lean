import data algebra.group .subgroup .finsubg theories.number_theory.pinat .cyclic

open nat finset fintype group_theory

-- useful for debugging
set_option formatter.hide_full_terms false

definition pred_p [reducible] (p : nat) : nat → Prop := λ n, n = p

section set_missing

lemma image_singleton {A B : Type} [hA: decidable_eq A] [hB: decidable_eq B] (f : A → B) (a : A) :
image f (insert a empty) =  insert (f a) empty :=
begin
rewrite image_insert
end

-- lemma mem_insert_empty {A : Type} [hA: decidable_eq A] {a x : A} : x ∈ (insert a ∅) → x = a :=
-- !set.eq_of_mem_singleton
--   -- assume Hmem,
--   -- or.elim (eq.subst (mem_insert_eq x a ∅) Hmem)
--   -- (λ x, x)
--   -- begin
--   --   intro Habs,
--   --   exact false.elim (not_mem_empty a Habs)
--   -- end

lemma insert_empty {A : Type} [hAdec : decidable_eq A] (a : A) (b : A) :
finset.insert a finset.empty = insert b empty → a = b :=
assume Heq_set,
have Hab : mem a (insert b empty), from (eq.subst Heq_set (mem_insert a empty)),
or.elim (eq.subst (mem_insert_eq a b empty) Hab) (take H, H)
begin
intro Habs,
exact false.elim (not_mem_empty a Habs)
end

end set_missing

-- section groupStructure

-- -- this is not actually what we want, as G is not necessarily finite
-- structure fingroup [class] (G : Type) extends group G :=
-- [finG : fintype G]

-- structure Fingroup := (carrier : Type) (struct : fingroup carrier)

-- attribute Fingroup.carrier [coercion]
-- attribute Fingroup.struct [instance]

-- -- we can now talk about g : G
-- example (FG : Fingroup) (g : FG) : g * 1  = g := mul_one g


-- structure fin_subg [class] (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] (H : finset G) extends is_finsubg H :=
-- [finG : fintype G]

-- structure Fin_subg (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] := (carrier : finset G) (struct : fin_subg G carrier)

-- attribute Fin_subg.carrier [coercion] [reducible]
-- attribute Fin_subg.struct [instance] [reducible]

-- -- of course this does not work, we need to make it apparent that
-- -- Fin_subg G is a finite type

-- -- how does Mathcomp do this? It seems that fingrouptype is an extension of fintype,
-- -- and that {group gT} is an extension of {set gT}

-- lemma struct_irrelevant (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] (H : finset G) (fsg1 : fin_subg G H) (fsg2 : fin_subg G H) :
--   fsg1 = fsg2 := sorry

-- lemma injective_projection (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] -- (H1 H2 : Fin_subg G)
-- :
--   function.injective (@Fin_subg.carrier G ambientG deceqG) := sorry
--   -- take (H1 : Fin_subg G) (H2 : Fin_subg G) Heq,
--   -- have foo : Fin_subg.struct H1 = (eq.subst Heq (Fin_subg.struct H2)), from struct_irrelevant G (Fin_subg.carrier H1) H1 H2,
--   _
--     -- @Fin_subg.rec_on G _ _ (λ x, @Fin_subg.carrier G _ _ H1 = @Fin_subg.carrier G _ _ x → H1 = x) H2 (take c s, _)

-- lemma finSubGroups [instance] (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] : fintype (Fin_subg G) := sorry

-- definition all_subgroups (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] : @finset.univ (finSubGroups G)

-- example : ∀ (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] , decidable (∀ (H : Fin_subg G), 1 ∈ H) :=
-- take G aG decG,
--   decidable_forall_finite


-- how can we talk about the set of all (automatically finite) subgroups of FG?


-- definition all_subgroups (G : Fingroup) (H : G) :=
-- { S : G | ∀ x, x ∈ S → x = x }

-- end groupStructure

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

section groups_missing

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

definition is_finsubg_prop [class] (A : finset G) : Prop :=
  1 ∈ A ∧ finset_mul_closed_on A ∧ finset_has_inv A

attribute is_finsubg_prop [reducible]

lemma is_finsub_is_finsubg_prop {A : finset G} : is_finsubg_prop A → is_finsubg A :=
  assume H,
  is_finsubg.mk (and.left H) (and.left (and.right H)) (and.right (and.right H))

local attribute finset_has_inv [reducible]

lemma decidable_is_finsubg_prop [instance] {A : finset G} : decidable (is_finsubg_prop A) := _

reveal decidable_is_finsubg_prop

lemma lagrange_div {H1 H2 : finset G} [H1gr : is_finsubg H1] [ H2gr : is_finsubg H2]
  (HS : subset H1 H2) :
  card H1 ∣ card H2 :=
  dvd_of_eq_mul _ _ _ (eq.subst !nat.mul_comm (lagrange_theorem HS))

end groups_missing

section PgroupDefs

parameter pi : ℕ → Prop
variable [Hdecpi : ∀ p, decidable (pi p)]

-- should we enforce H being a group at this point ? no

definition pgroup [reducible] (H : finset G) := is_pi_nat pi (card H)
-- reveal pgroup
-- print pgroup

-- the index of the subgroup A inside the group B
definition index [reducible] (A B : finset G) -- (Psub : finset.subset A B)
:= finset.card (fin_lcosets A B)

definition pi_subgroup (H1 H2 : finset G) := subset H1 H2 ∧ pgroup H1

definition pi_elt (pi : ℕ → Prop) (x : G) : Prop := is_pi_nat pi (order x)

definition Hall [reducible] (A B : finset G) :=
subset A B ∧ coprime (card A) (index A B)

include Hdecpi
lemma pgroup_dec (H : finset G) : decidable (pgroup H) := _

definition pHall [reducible] (A B : finset G) :=
subset A B ∧ pgroup A ∧ is_pi'_nat pi (index A B)

end PgroupDefs

section sylows

-- the set of p-Sylows of a subset A
definition Syl [reducible] (p : nat) (A : finset G) :=
{ S ∈ finset.powerset A | is_finsubg_prop S ∧ pHall (pred_p p) S A }

-- Definition Sylow A B := p_group B && Hall A B.
definition is_sylow p (A B : finset G) := pgroup (pred_p p) A ∧ Hall A B

definition is_in_Syl [class] (p : nat) (A S : finset G) := S ∈ Syl p A

end sylows

lemma sylow_finsubg_prop [instance] (p : nat) (A : finset G) (S : finset G)  [HSyl : is_in_Syl p A S] : is_finsubg_prop S :=
  and.left (of_mem_sep HSyl)

reveal is_finsub_is_finsubg_prop

definition sylow_is_finsubg [instance] (p : nat) (A S : finset G) [HSyl : is_in_Syl p A S] : is_finsubg S
:= is_finsub_is_finsubg_prop (sylow_finsubg_prop p A S)

-- variables (p : nat) (A S : finset G) (H : S ∈ Syl p A)
-- include H

-- set_option pp.implicit true

example (p : nat) (A S : finset G) (H : is_in_Syl p A S)
: is_finsubg S := _ -- @sylow_is_finsubg G _ _ _ p A S H  --(sylow_is_finsubg _)

-- only true if they actually are groups
lemma pgroupS {pi : ℕ → Prop} {H1 H2 : finset G} [H1gr : is_finsubg H1] [ H2gr : is_finsubg H2] :
  subset H1 H2 → pgroup pi H2 → pgroup pi H1 :=
    assume HS HpiH2,
   pinat_dvd (lagrange_div HS) HpiH2

lemma pisubgroupS {pi : ℕ → Prop} (H2 : finset G) {H1 H3 : finset G}
      [H1gr : is_finsubg H1] [ H2gr : is_finsubg H2] (HS : subset H1 H2) :
      pi_subgroup pi H2 H3 → pi_subgroup pi H1 H3 :=
      assume Hpi23,
      and.intro
      (subset.trans HS (and.left Hpi23))
      (pgroupS HS (and.right Hpi23))



-- lemma lcoset_one (B : finset G): (fin_lcosets B '{(1:G)}) = insert (fin_lcoset B 1) empty :=
-- let f := (λ x, fin_lcoset B x) in
--   image_singleton f


lemma inj_fin_lcoset_one -- (B : finset G)
: function.injective (fin_lcoset '{(1:G)}) :=
take (x : G) (a : G),
assume Hxa,
have H1 : ∀ (x : G), fin_lcoset (insert (1 : G) empty) x = image (lmul_by x) (insert 1 empty), from take (x : G), rfl,
have H2 : ∀ (x : G), image (lmul_by x) (insert (1 : G) empty) = insert (lmul_by x (1:G)) empty , from take x, begin
apply image_singleton
end,
have H : ∀ (x : G),  fin_lcoset (insert (1 : G) empty) x = insert (lmul_by x 1) empty, from take x,
calc
   fin_lcoset (insert (1 : G) empty) x = image (lmul_by x) (insert 1 empty) : {H1 x}
   ...                                 = insert (lmul_by x 1) empty         : {H2 x},
have Hx : fin_lcoset (insert (1 : G) empty) x = insert (lmul_by x 1) empty, from (H x),
have Ha : fin_lcoset (insert (1 : G) empty) a = insert (lmul_by a 1) empty, from (H a),
have showdown : insert (lmul_by x 1) empty =  insert (lmul_by a 1) empty, from eq.subst Hx (eq.subst Ha Hxa),
insert_empty x a (eq.subst (lmul_one_id x) (eq.subst (lmul_one_id a) showdown))

lemma index_one (B : finset G)  : index '{(1:G)} B = finset.card B :=
  calc
  index '{(1:G)} B = finset.card (fin_lcosets '{(1:G)}  B) : rfl
  ...              = finset.card (image (fin_lcoset '{(1:G)}) B) : rfl
-- problem here : fin_lcoset '{(1:G)} has type G → finset G instead of
-- B → finset G
  ...              = finset.card B : sorry --(card_eq_card_image_of_inj (inj_fin_lcoset_one))
  ...              = _ : sorry

lemma Hall1 (A : finset G) [h_A_gr : is_finsubg A] : Hall '{(1:G)} A :=
  and.intro (subset_one_group A h_A_gr)
  begin
    rewrite (index_one A),
    rewrite card1,
    exact (gcd_one_left (finset.card A))
  end

lemma p_group1 (p : nat) : pgroup (pred_p p) '{(1:G)} :=
and.intro
  begin
    rewrite card1,
    apply nat.le_refl
  end
  (take p Hp,
  absurd Hp (not_mem_empty p)
  )
-- lemma sylow1 p (B : finset G): is_sylow p '{(1:G)} B  := _
