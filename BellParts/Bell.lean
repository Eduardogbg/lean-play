import BellParts.Partition
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
-- TODO: is there a way to get all imports I depend on directly
-- so it's more explicit which ones I need?

variable {X: Type} [DecidableEq X] (S: Finset X)

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
  simp only [bell_term, Nat.choose_succ_self, zero_mul, zero_add]

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

-- TODO: switch occurences of this predicate for powersetCard directly
-- so we can throw this out
instance fintype_powersetCard_as_predicate
  (k: Fin (S.card + 1)):
  Fintype { x // x ∈ S.powerset ∧ x.card = ↑k } :=
by
  apply Fintype.ofFinset (S.powersetCard ↑k)
  intro x
  simp [Finset.mem_powersetCard, Finset.mem_powerset]
  rfl

theorem bell_numbers_count_partitions:
  ∀ n : ℕ,
  ∀ S: Finset X,
    S.card = n → finset_partition_count S = bell n :=
by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold finset_partition_count at ih
    intro S S_card
    cases n with
    | zero =>
      have S_empty : S = ∅ := Finset.card_eq_zero.mp S_card
      rw [S_empty]
      rw [finset_partition_count, bell, bell_term]
      rw [Fintype.card_eq_one_iff]
      use the_empty_partition
      exact partition.parts_of_empty_but_better
    | succ n =>
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [S_card]; exact Nat.zero_lt_succ n)

      let S' := S \ {x}
      have x_nin_S' : x ∉ S' := by rw [Finset.mem_sdiff]; simp []

      have S'_card : S'.card = n :=
      by
        rw [Finset.card_sdiff]
        · simp [S_card]
        · exact Finset.singleton_subset_iff.mpr hx
      have S_eq : S = insert x S' :=
      by
        unfold S'
        rw [
          Finset.insert_eq,
          Finset.union_sdiff_of_subset
            (Finset.singleton_subset_iff.mpr hx)
        ]

      rw [S_eq, finset_partition_count]
      have bij := partition.insert_recurrence x x_nin_S'
      rw [Fintype.card_congr bij]
      rw [Fintype.card_congr sigma_powerset_by_card]

      convert Fintype.card_sigma

      -- key lemma, idk if it's possible to abstract tho,
      -- because it depends on ih. I guess we could take it
      -- as an input but it somewhat defeats the purpose of
      -- abstracting it from this inductive proof.
      have part_card_by_supp_card :
        ∀ k : Fin (S'.card + 1),
        ∀ t : { x // x ∈ S'.powerset ∧ x.card = ↑k },
        Fintype.card (partition (S' \ ↑t)) = bell (n - ↑k) :=
      by
        intro k t
        have card_eq : (S' \ ↑t).card = n - ↑k := by
          rw [Finset.card_sdiff]
          · rw [← S'_card]
            rw [t.prop.2]
          · exact Finset.mem_powerset.mp t.prop.1
        have lt : n - ↑k < n + 1 := by omega
        exact ih (n - ↑k) lt (S' \ ↑t) card_eq

      have card_powersetCard_as_predicate:
        (k: Fin (S'.card + 1)) →
        Fintype.card { x // x ∈ S'.powerset ∧ x.card = ↑k } = n.choose ↑k :=
      by
        intro k
        rw [
          Fintype.card_congr (powersetCard_as_predicate k),
          Fintype.card_coe,
          Finset.card_powersetCard
        ]
        conv_lhs => arg 1; rw [S'_card]

      have :
        (k: Fin (S'.card + 1))
          → Fintype.card
          ((s : { x // x ∈ S'.powerset ∧ x.card = ↑k }) × partition (S' \ ↑s))
        = (Nat.choose n k * bell (n - k)) :=
      by
        intro k
        rw [Fintype.card_sigma]
        simp only [S']
        simp only [S_eq]
        rw [Finset.insert_sdiff_of_mem S' (Finset.mem_singleton.mpr rfl)]
        simp [Finset.sdiff_eq_self_of_disjoint, x_nin_S']
        simp_rw [part_card_by_supp_card k]
        rw [Finset.sum_const, Finset.card_univ]
        change
          Fintype.card { x_1 // x_1 ∈ S'.powerset ∧ x_1.card = ↑k } • bell (n - ↑k)
          = n.choose ↑k * bell (n - ↑k)
        simp [S'_card]
        left
        exact card_powersetCard_as_predicate k

      conv_rhs => arg 2; ext i; rw [this]
      rw [bell_recurrence]
      have : S'.card + 1 = n + 1 := by omega
      rw [← Fin.sum_univ_eq_sum_range]
      conv_rhs =>
        arg 2; ext i; arg 1;
        rw [← Nat.choose_symm (S'_card ▸ Nat.le_of_lt_succ (Fin.is_lt i))]

      rw [this]
      have : ∀i: Fin (n + 1), (n - ↑i) = Fin.rev i :=
      by
        intro i
        rw [Fin.rev]
        simp
      conv_rhs => arg 2; intro i; rw [this i]
      let f : Fin (n + 1) → ℕ := fun j => n.choose ↑j * bell ↑j
      have : ∀k: Fin (n + 1), (n - (n - ↑k)) = ↑k := by omega
      -- TODO: there's already a result Fin.revOrderIso that should
      -- be able to be converted into a bijection
      rw [Fintype.sum_bijective Fin.rev]
      .
        constructor
        .
          unfold Function.Injective
          simp
        .
          unfold Function.Surjective
          intro b
          conv => arg 1; ext a; rw [Fin.rev]
          conv => arg 1; ext a; rw [Fin.eq_mk_iff_val_eq]
          simp
          use n - b
          have : ↑(↑n - b) = n - ↑b :=
          by
            simp
            rw [Fin.last]
            rw [Fin.sub_def]
            simp
            have h1 : (n + 1) - ↑b + n = (n - ↑b) + (n + 1) := by omega
            rw [h1]
            rw [Nat.add_mod_right (n - ↑b) (n + 1)]
            have hb : ↑b ≤ n := Nat.lt_succ_iff.mp (Fin.is_lt b)
            have : n - ↑b < n + 1 := by omega
            exact Nat.mod_eq_of_lt this
          rw [this]
          omega
      .
        intro i
        rw [Fin.rev]
        simp
        rw [Nat.choose_symm]
        rw [this i]
        exact Nat.le_of_lt_succ i.isLt
