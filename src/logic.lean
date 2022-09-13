
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro np,
  exact np hp,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_contradiction pboom,
  exact nnp pboom,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
    exact doubleneg_elim P,
    exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro poq,
  cases poq with hp hq,
    right,
      exact hp,
    left,
      exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro peq,
  split,
    cases peq with hp hq,
      exact hq,
    cases peq with hp hq,
      exact hp,  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros npoq hp,
  cases npoq with np hq,
    contradiction,
    exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros poq np,
  cases poq with hp hq,
    contradiction,
    exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros piq nq hp,
  have hq: Q := piq hp,
  exact nq hq,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros nqinp hp,
  by_contradiction nq,
  have np: ¬P := nqinp nq,
  exact np hp,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split, 
    exact impl_as_contrapositive P Q,
    exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_ponp,
  have ponp: (P∨¬P),
    right,
    intro hp,
    apply n_ponp,
      left,
      exact hp,
  exact n_ponp ponp,  
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros piq_ip np,
  have piq: (P → Q),
    intro hp,
    contradiction,
  have p:P  := piq_ip piq,
  exact np p,  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros poq npenq,
  cases poq with hp hq,
    cases npenq with np nq,
      exact np hp,
    cases npenq with np nq,
      exact nq hq,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros peq nponq,
  cases nponq with np nq,
    cases peq with hp hq,
      exact np hp,
    cases peq with hp hq,
      exact nq hq,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_poq,
  split,
    intro hp,
      have poq: (P∨Q),
        left,
        exact hp,
      exact n_poq poq,
    intro hq,
      have poq: (P∨Q),
        right,
        exact hq,
      exact n_poq poq,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros npenq poq,
  cases poq with hp hq,
    cases npenq with np nq,
      exact np hp,
    cases npenq with np nq,
      exact nq hq,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro n_peq,
  by_contradiction nq_o_np,
  apply nq_o_np,
    right,
    intro hp,
  apply nq_o_np,
    left,
    intro hq,
  exact n_peq ⟨hp,hq⟩,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros nqonp peq,
  cases nqonp with nq np,
    cases peq with hp hq,
      exact nq hq,
    cases peq with hp hq,
      exact np hp,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split, 
    exact demorgan_conj P Q,
    exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
    exact demorgan_disj P Q,
    exact demorgan_disj_converse P Q, 
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pe_qor,
  cases pe_qor with hp qor,
    cases qor with hq hr,
      left,
      split,
        exact hp,
        exact hq,
      right,
      split,
        exact hp,
        exact hr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro peq_o_per,
  split,
    cases peq_o_per with peq per,
      cases peq with hp hq,
        exact hp,
      cases per with hp hr,
        exact hp,
    cases peq_o_per with peq per,
      left, 
        cases peq with hp hq,
          exact hq,
      right,
        cases per with hp hr,
          exact hr,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro po_qer,
  split,
    cases po_qer with hp qer,
      left,
        exact hp,
      cases qer with hq hr,
        right,
          exact hq,
    cases po_qer with hp qer,
      left, 
        exact hp,
      cases qer with hq hr,
        right, 
          exact hr,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro poq_e_por,
  cases poq_e_por with poq por,
    cases poq with hp hq,
      left,
        exact hp,
      cases por with hp hr,
        left,
          exact hp,
        right,
          split,
            exact hq,
            exact hr,  
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros peq_ir hp hq, 
  exact peq_ir ⟨hp,hq⟩,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros pi_qir peq,
  cases peq with hp hq,
    exact pi_qir hp hq,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
    exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
    exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro peq,
  cases peq with hp hq,
    exact hp,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  cases peq with hp hq,
    exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
    exact weaken_conj_right P P,
    intro hp,
    split,
      exact hp,
      exact hp,  
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
    intro pop,
    cases pop with hp hp,
      exact hp,
      exact hp,
    exact weaken_disj_right P P,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros n_eapa a hp,
  exact n_eapa ⟨a,hp⟩,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros a_npa eapa,
  cases eapa with a pa,
    exact a_npa a pa,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro n_apa,
  by_contradiction ea_npa,
  apply n_apa,
    intro a,
    by_contradiction npa,
  apply ea_npa,
    existsi a,
    intro pa,
  exact npa pa,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros ea_npa apa,
  cases ea_npa with a npa,
  have pa : P a := apa a,
  exact npa pa,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
    apply demorgan_forall,
    apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split, 
    apply demorgan_exists,
    apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros eapa a_npa,
  cases eapa with a pa,
  exact a_npa a pa,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros apa ea_npa,
  cases ea_npa with a npa,
  have pa : P a := apa a,
  exact npa pa,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros n_ea_npa a,
  by_contradiction np,
  exact n_ea_npa ⟨ a,np ⟩, 
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro n_a_npa,
  by_contradiction eapa,
  apply n_a_npa,
    intro a,
    intro pa,
  apply eapa,
    existsi a,
    exact pa,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
    apply forall_as_neg_exists,
    apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
    apply exists_as_neg_forall,
    apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro ea_paeqa,
  split,
    cases ea_paeqa  with a paeqa,
      existsi a,
      cases paeqa with pa qa,
        exact pa,
    cases ea_paeqa with a paeqa,
      existsi a,
      cases paeqa with pa qa,
        exact qa,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro ea_paoqa,
  cases ea_paoqa with a paoqa,
  cases paoqa with pa qa,
    left,
      existsi a,
      exact pa,
    right, 
      existsi a,
      exact qa,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro eapa_o_eaqa,
  cases eapa_o_eaqa with eapa eaqa,
    cases eapa with a pa,
      existsi a,
      left,
        exact pa,
    cases eaqa with a qa,
      existsi a,
      right,
        exact qa,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro a_paeqa,
  split,
    intro a,
    have paeqa : P a ∧ Q a := a_paeqa a,
    cases paeqa with pa qa,
      exact pa,
    intro a, 
    have paeqa : P a ∧ Q a := a_paeqa a,
    cases paeqa with pa qa,
      exact qa,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros apa_e_aqa a,
  cases apa_e_aqa with apa aqa,
    split,
      exact apa a,
      exact aqa a,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros apa_o_aqa a,
  cases apa_o_aqa with apa aqa,
    left,
      exact apa a,
    right,
      exact aqa a,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
