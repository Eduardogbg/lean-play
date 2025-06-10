import BellParts.Partition
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma

def bell_term: ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | n+1, k+1 =>
    have term := Nat.choose n (k + 1) * bell_term (k + 1) k
    have rest := bell_term (n + 1) k
    term + rest

def bell (n : ℕ) : ℕ := bell_term n n

lemma bell_term_diag_simpl (x : ℕ) :
  bell_term (x+1) (x+1) = bell_term (x+1) x :=
by
  simp only [bell_term]
  unfold bell_term
  have h_choose_zero : Nat.choose x (x+1) = 0 := by
    apply Nat.choose_eq_zero_of_lt
    exact Nat.lt_succ_self x
  rw [h_choose_zero, Nat.zero_mul]
  dsimp
  rw [Nat.zero_add]

lemma bell_eq_bell_term_succ_prev (x : ℕ) :
  bell (x+1) = bell_term (x+1) x :=
by
  rw [bell, bell_term_diag_simpl x]

lemma bell_term_recurrence (n k : ℕ) (h : k ≤ n) :
  bell_term (n+1) k = (Finset.range (k + 1)).sum (fun j => Nat.choose n j * bell j) :=
by
  induction k with
  | zero =>
    simp [bell, bell_term]
  | succ k ih =>
    have k_lt_n : k ≤ n := by linarith
    simp only [bell_term]
    have bell_to_term : bell_term (k + 1) k = bell (k + 1) :=
      (bell_eq_bell_term_succ_prev k).symm
    rw [bell_to_term, ih k_lt_n]
    nth_rewrite 2 [Finset.sum_range_succ]
    omega -- todo: benchmark omega vs linarith

theorem bell_recurrence (n: ℕ) :
  bell (n + 1) = (Finset.range (n + 1)).sum (fun k => Nat.choose n k * bell k) :=
by
  rw [bell_eq_bell_term_succ_prev]
  simp only [le_refl, bell_term_recurrence]

-- why couldn't lean synthetize this on its own?
-- how do I finish the proof?
-- instance this_should_have_been_synth
--   (X: Type) [DecidableEq X]
--   (S: Finset X):
--   Fintype (Σ (s : S.powerset), partition X (S \ ↑s)) :=
-- by
--   sorry
instance this_should_have_been_synth_2
  (X: Type) [DecidableEq X]
  (S: Finset X):
  Fintype (Σ m : Fin (S.card + 1), Σ s : { x // x ∈ S.powerset ∧ x.card = m }, partition X (S \ ↑s)) := by sorry

instance synth_wtf
  (X: Type) [DecidableEq X]
  (S: Finset X):
  (i : Fin (S.card + 1)) → Fintype ((fun m ↦ (s : { x // x ∈ S.powerset ∧ x.card = ↑m }) × partition X (S \ ↑s)) i) := by sorry

theorem bell_numbers_count_partitions
  (X : Type) [DecidableEq X] :
  ∀ n : ℕ, ∀ S : Finset X, S.card = n → finset_partition_count X S = bell n :=
by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold finset_partition_count at ih
    intro S hS
    cases n with
    | zero =>
      have S_empty : S = ∅ := Finset.card_eq_zero.mp hS
      rw [S_empty]
      rw [finset_partition_count, bell, bell_term]
      rw [Fintype.card_eq_one_iff]
      use the_empty_partition X
      intro y
      exact partition.parts_of_empty_but_better y
    | succ n =>
      -- this depends on choice? maybe avoid choice if it does...
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hS]; exact Nat.zero_lt_succ n)
      let S' := S \ {x}
      have hS' : S'.card = n :=
      by
        rw [Finset.card_sdiff]
        · simp [hS]
        · exact Finset.singleton_subset_iff.mpr hx
      have S_eq : S = insert x S' :=
      by
        ext a
        simp [S', Finset.mem_sdiff]
        constructor
        · intro ha
          by_cases h : a = x
          · exact Or.inl h
          · exact Or.inr ⟨ha, h⟩
        · intro h
          cases h with
          | inl h => rw [h]; exact hx
          | inr h => exact h.1

      rw [S_eq, finset_partition_count]
      have bij := partition.insert_recurrence S' x (by simp [S'])
      rw [Fintype.card_congr bij]
      rw [Fintype.card_congr (sigma_powerset_by_card X S')]

      convert Fintype.card_sigma
      .
        -- todo: use ih to prove this here
        have :
          (k: Fin (S'.card + 1))
            → Fintype.card
            ((s : { x // x ∈ S'.powerset ∧ x.card = ↑k }) × partition X (S' \ ↑s))
          = (Nat.choose n k * bell k) :=
        by
          -- todo: need crazy sigma shit but also that powerset
          -- filtered by card is equal to (n choose k)
          sorry

        -- gotta apply hS' in the sum index too
        conv_rhs =>
          arg 2
          ext i
          rw [this]

        rw [bell_recurrence]
        -- gotta prove that summing over Fin is the same as over
        -- Finset.range
        sorry
      . sorry
