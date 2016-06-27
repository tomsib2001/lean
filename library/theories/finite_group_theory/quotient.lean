-- some extra lemmas about group quotients

import data .subgroup .finsubg .extra_finsubg algebra.group

open group_theory finset subtype

namespace group_theory

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

variables (H : finset G) [HfinsubgH : is_finsubg H]
include HfinsubgH
definition quotH := lcoset_type (normalizer H) H

set_option formatter.hide_full_terms false
variable {H}
definition get_lcoset_type (g : G) (HgH : g ∈ normalizer H) : lcoset_type (normalizer H) H :=
(tag (fin_lcoset H g) (exists.intro g (and.intro HgH rfl)))

definition natural_morphism (g : G) : lcoset_type (normalizer H) H := if HgH : g ∈ normalizer H then get_lcoset_type g HgH else fin_coset_one  


definition finset_to_lcoset_type (Kbar : finset (finset G)) 
  (H_fin_cosets : ∀ s, s ∈ Kbar → is_fin_lcoset (normalizer H) H s) :
  finset (lcoset_type (normalizer H) H) := sorry
  -- _ (λ x, tag x (H_fin_cosets x _)) _




-- definition proj (K : (finset G)) : finset (lcoset_type (normalizer H) H) :=
-- all_lcosets (normalizer H) H

-- lemma lift1 (Kbar : finset (finset G)) [HfinsubK : is_finsubg Kbar] :
--   exists (K : finset G) , H ⊆ K ∧ is_finsubg_prop G K -- ∧ (set.map elt_of Kbar = fin_lcosets (normalizer H) K) -- can't even write this down
--   :=
--   have H1inKbar : fin_coset_one ∈ Kbar, from !finsubg_has_one,
--   exists.intro (fin_coset_Union Kbar)
--   (and.intro
--    (iff.elim_right (subset_iff_all _ _) (all_of_forall (take a memaH, iff.elim_right (mem_Union_iff _ _ _)
--   (exists.intro fin_coset_one (and.intro H1inKbar memaH)))))
--    (is_finsubg_prop_is_finsubg _))


lemma lift2 (Kbar : finset (lcoset_type (normalizer H) H)) [HfinsubK : is_finsubg Kbar] :
  exists (K : finset G) , H ⊆ K ∧ is_finsubg_prop G K ∧ (Kbar = fin_lcosets (normalizer H) K) -- can't even write this down
  :=
  have H1inKbar : fin_coset_one ∈ Kbar, from !finsubg_has_one,
  exists.intro (fin_coset_Union Kbar)
  (and.intro
   (iff.elim_right (subset_iff_all _ _) (all_of_forall (take a memaH, iff.elim_right (mem_Union_iff _ _ _)
  (exists.intro fin_coset_one (and.intro H1inKbar memaH)))))
   (is_finsubg_prop_is_finsubg _))


end group_theory
