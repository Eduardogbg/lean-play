import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Algebra.Basic


-- from data.setoid.partitions
-- youtu.be/FEKsZj3WkTY
@[ext] structure partition (X : Type) [DecidableEq X] (S: Finset X) where
  family : Finset (Finset X)
  non_empty: ∀ c ∈ family, c ≠ ∅
  covers: family.biUnion id = S
  disjoint: ∀ c ∈ family, ∀ d ∈ family, c ∩ d ≠ ∅ → c = d

def partition.mk_if_valid {X: Type} [DecidableEq X] (S: Finset X) (family: Finset (Finset X)) : Option (partition X S) :=
  if non_empty : (∀ c ∈ family, c ≠ ∅)
  then if covers : (family.biUnion id = S)
       then if disjoint : (∀ c ∈ family, ∀ d ∈ family, c ∩ d ≠ ∅ → c = d)
            then some {
              family := family,
              non_empty := non_empty,
              covers := covers,
              disjoint := disjoint
            }
            else none
       else none
  else none


-- TODO: how to name this?
lemma partition.mk_if_valid_id_family
  {X: Type}
  [DecidableEq X]
  (S: Finset X)
  (fam: Finset (Finset X))
  (part: partition X S)
  (mk_is_some: partition.mk_if_valid S fam = some part):
  part.family = fam :=
by
    unfold partition.mk_if_valid at mk_is_some
    split_ifs at mk_is_some with h₁ h₂ h₃; simp only [Option.some_inj] at mk_is_some
    rw [← mk_is_some]


lemma partition.mk_if_valid_inj_some {X: Type} [DecidableEq X] (S: Finset X) :
  ∀ (a a' : Finset (Finset X)), ∀ b ∈ mk_if_valid S a, b ∈ mk_if_valid S a' → a = a' :=
by
  intros fam1 fam2 p p_in_fam1 p_in_fam2
  rw [Option.mem_def] at p_in_fam1 p_in_fam2

  have fam_eq_fam1 : p.family = fam1 :=
    partition.mk_if_valid_id_family S fam1 p p_in_fam1
  have fam_eq_fam2 : p.family = fam2 :=
    partition.mk_if_valid_id_family S fam2 p p_in_fam2

  rw [← fam_eq_fam1, fam_eq_fam2]

lemma partition.family_in_double_powerset {X} [DecidableEq X] (S: Finset X) (part: partition X S) :
  part.family ∈ (S.powerset.powerset) :=
by
  rw [Finset.mem_powerset]
  intro c c_in_fam
  rw [Finset.mem_powerset]
  intro x x_in_c
  have x_in_union : x ∈ part.family.biUnion (id : Finset X → Finset X) := by
    apply Finset.mem_biUnion.mpr
    use c
    constructor
    . exact c_in_fam
    . exact x_in_c
  rw [part.covers] at x_in_union
  exact x_in_union

lemma partition.in_double_powerset_filterMap_mk_if_valid
  (X: Type) [DecidableEq X] (S: Finset X) (part : partition X S):
  part ∈ (S.powerset.powerset).filterMap
    (partition.mk_if_valid S)
    (partition.mk_if_valid_inj_some S) :=
by
  simp_rw [Finset.mem_filterMap]
  use part.family
  constructor
  ·
    rw [Finset.mem_powerset]
    intro c c_in_fam
    rw [Finset.mem_powerset]
    intro x x_in_c
    have x_in_union : x ∈ part.family.biUnion (id : Finset X → Finset X) := by
      apply Finset.mem_biUnion.mpr
      use c
      constructor
      · exact c_in_fam
      · exact x_in_c
    rw [part.covers] at x_in_union
    exact x_in_union
  ·
    unfold partition.mk_if_valid
    split_ifs with non_empty covers disjoint
    · apply Option.some_inj.mpr
      ext
      · rfl
    · exact disjoint part.disjoint
    . exact covers part.covers
    . exact non_empty part.non_empty

-- not the shortest neatier proof but it's constructive and educational
instance partition.Fintype (X : Type) [DecidableEq X] (S: Finset X) : Fintype (partition X S) where
  elems := (S.powerset.powerset).filterMap (partition.mk_if_valid S) (partition.mk_if_valid_inj_some S)
  complete :=
  by
    intro part
    exact partition.in_double_powerset_filterMap_mk_if_valid X S part

def finset_partition_count (X : Type) [DecidableEq X] (S : Finset X): ℕ :=
  Fintype.card (partition X S)

def the_empty_partition (X : Type) [DecidableEq X] : partition X ∅ := {
  family := ∅,
  non_empty := fun c hc => (Finset.not_mem_empty c hc).elim
  covers := Finset.biUnion_empty
  disjoint := fun c hc => (Finset.not_mem_empty c hc).elim
}

lemma singleton_empty_powerset {X} [DecidableEq X]: ({∅}: (Finset (Finset X))).powerset = {∅, {∅}} := by
  ext fam
  constructor
  · intro h
    exact h
  · intro h
    exact h

lemma partitions_of_empty  {X: Type} [DecidableEq X] :
  Finset.filterMap
    (partition.mk_if_valid ∅)
    ({∅, {∅}}: (Finset (Finset (Finset X))))
    (partition.mk_if_valid_inj_some ∅)
  =  {the_empty_partition X} :=
by
  ext part
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, or_iff_left_iff_imp, iff_def]
  constructor
  · intro fam_part_if_valid
    ext
    constructor
    . intros a_in_fam
      rw [the_empty_partition]
      simp only [Finset.not_mem_empty]
      have : part.family = ∅ :=
      by
        unfold partition.mk_if_valid at fam_part_if_valid
        rw [Finset.mem_filterMap] at fam_part_if_valid
        rcases fam_part_if_valid with ⟨x, x_partition_if_valid⟩
        rcases x_partition_if_valid with ⟨x_in_powerset, x_part_if_valid⟩
        split_ifs at x_part_if_valid with non_empty covers disjoint
        rw [Option.some_inj] at x_part_if_valid
        simp only [Finset.mem_insert, Finset.mem_singleton] at x_in_powerset
        have x_empty_set : x = ∅ := by
          rcases x_in_powerset with (rfl | x_in_powerset)
          . exact rfl
          .
            exfalso
            apply absurd non_empty
            simp only [ne_eq, Finset.forall_mem_not_eq', Decidable.not_not]
            rw [x_in_powerset]
            rw [Finset.mem_singleton]
        obtain ⟨_, _⟩ := x_part_if_valid
        simp only [x_empty_set]
      apply absurd a_in_fam
      rw [this]
      simp only [Finset.not_mem_empty, not_false_eq_true]
    unfold the_empty_partition
    simp only [Finset.not_mem_empty, IsEmpty.forall_iff]
  .
    -- TODO: this should be trivialer
    intro part_empty
    rcases part_empty with ⟨_, _⟩
    unfold partition.mk_if_valid
    rw [Finset.mem_filterMap]
    use ∅
    constructor
    . simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    .
      split_ifs with non_empty covers disjoint
      rw [Option.some_inj]
      unfold the_empty_partition
      rfl
      .
        simp only [Finset.not_mem_empty, IsEmpty.forall_iff] at disjoint
        rw [implies_true, not_true_eq_false] at disjoint
        exact disjoint
      . simp only [Finset.biUnion_empty, not_true_eq_false] at covers
      .
        simp only [Finset.not_mem_empty, ne_eq, IsEmpty.forall_iff] at non_empty
        rw [implies_true, not_true_eq_false] at non_empty
        exact non_empty

lemma partition.parts_of_empty_but_better {X: Type} [DecidableEq X] (part: partition X ∅) :
  part = the_empty_partition X :=
by
  have h1 : part ∈ (∅ : Finset X).powerset.powerset.filterMap
    (partition.mk_if_valid ∅)
    (partition.mk_if_valid_inj_some ∅) :=
    partition.in_double_powerset_filterMap_mk_if_valid X ∅ part

  have h2 : (∅ : Finset X).powerset = {∅} := Finset.powerset_empty
  have h3 : ({∅} : Finset (Finset X)).powerset = {∅, {∅}} := singleton_empty_powerset
  rw [h2, h3] at h1
  rw [partitions_of_empty] at h1
  exact Finset.mem_singleton.mp h1

lemma card_partitions_of_empty {X: Type} [Inhabited X] [DecidableEq X] :
  Fintype.card (partition X ∅) = 1 :=
by
  unfold Fintype.card
  unfold Finset.univ
  unfold Fintype.elems
  unfold partition.Fintype
  simp only [Finset.powerset_empty]
  rw [singleton_empty_powerset, partitions_of_empty]
  unfold the_empty_partition
  rw [Finset.card_singleton]

lemma finset_partition_count_recurrence
  {X : Type} [DecidableEq X] [Inhabited X]
  (n : ℕ)
  (S : Finset X)
  (s_card : S.card = n + 1) :
  finset_partition_count X S =
    (Finset.range (n + 1)).sum
    (fun k => Nat.choose n k *
      (finset_partition_count X
        (Finset.empty.image (fun (_ : Finset.range (n - k)) => default) )
      )
    ) :=
  by
    sorry

-- readme: it's only called forward because of the direction
-- we defined the bijection but it definitely feels more backwards
def partition.insert_recurrence_forward
  {X: Type} [DecidableEq X]
  (S: Finset X)
  (x: X)
  (x_not_in_S: x ∉ S):
  partition X (insert x S) → (s : { x // x ∈ S.powerset }) × partition X (S \ ↑s) :=
by
  intro part_insert
  have x_in_insert: x ∈ (insert x S) := Finset.mem_insert_self x S
  have x_in_union : x ∈ part_insert.family.biUnion id :=
  by
    rw [part_insert.covers]
    exact x_in_insert
  rw [Finset.mem_biUnion] at x_in_union

  let blocks_with_x := part_insert.family.filter (fun b => x ∈ b)
  have exactly_one_x_block : blocks_with_x.card = 1 := by
    rw [Finset.card_eq_one]
    unfold blocks_with_x
    obtain ⟨block, block_in_family, x_in_block⟩ := x_in_union
    rw [id] at x_in_block
    use block
    ext b
    constructor
    .
      intros b_in_family_x_in_b
      obtain ⟨b_in_family, x_in_b⟩ := Finset.mem_filter.mp b_in_family_x_in_b
      have h : b ∩ block ≠ ∅ :=
      by
        rw [← Finset.nonempty_iff_ne_empty]
        use x
        rw [Finset.mem_inter]
        exact ⟨x_in_b, x_in_block⟩
      rw [Finset.mem_singleton]
      exact part_insert.disjoint b b_in_family block block_in_family h
    .
      rw [Finset.mem_singleton]
      intro b_eq_block
      subst b_eq_block
      rw [Finset.mem_filter]
      exact ⟨block_in_family, x_in_block⟩

  let block := blocks_with_x.biUnion id
  have ⟨block_in_family, x_in_block⟩:
    block ∈ part_insert.family ∧ x ∈ block :=
  by
    rw [Finset.card_eq_one] at exactly_one_x_block
    obtain ⟨unique_block, h_eq⟩ := exactly_one_x_block
    have : block = unique_block :=
    by
      unfold block
      simp [h_eq, Finset.biUnion_singleton, id]
    rw [this]
    have : unique_block ∈ blocks_with_x := by simp only [Finset.mem_singleton, h_eq]
    rw [Finset.mem_filter] at this
    exact this

  let s := block ∩ S
  have s_subset : s ⊆ S := Finset.inter_subset_right
  have s_in_S_powerset: s ∈ S.powerset := Finset.mem_powerset.mpr s_subset

  have part_insert_in_double_powerset : part_insert.family ∈ (insert x S).powerset.powerset :=
    partition.family_in_double_powerset (insert x S) part_insert

  let rest_family := part_insert.family \ {block}

  -- todo: abstract this somehow?
  let rest_partition : partition X (S \ s) := {
    family := rest_family,
    non_empty := by
      intros c hc
      rw [Finset.mem_sdiff] at hc
      exact part_insert.non_empty c hc.1,
    -- todo: especially covers, abstract it
    covers := by
      ext y
      rw [Finset.mem_biUnion, Finset.mem_sdiff]
      simp only [id]
      constructor
      ·
        intro h
        obtain ⟨c, c_in_rest, y_in_c⟩ := h
        obtain ⟨c_in_family, c_nin_singleton_block⟩ := Finset.mem_sdiff.mp c_in_rest
        have c_ne_block : c ≠ block := Finset.not_mem_singleton.mp c_nin_singleton_block
        constructor
        ·
          have y_in_insert : y ∈ insert x S :=
            part_insert.covers ▸ Finset.mem_biUnion.mpr ⟨c, c_in_family, y_in_c⟩
          cases Finset.mem_insert.mp y_in_insert with
          | inl h =>
            subst h
            have c_eq_block : c = block :=
              part_insert.disjoint c c_in_family block block_in_family
              (by
                rw [← Finset.nonempty_iff_ne_empty, Finset.Nonempty]
                use y
                rw [Finset.mem_inter]
                exact ⟨y_in_c, x_in_block⟩)
            exact absurd c_eq_block c_ne_block
          | inr h => exact h
        ·
          intro y_in_s
          have y_in_block : y ∈ block := (Finset.mem_inter.mp y_in_s).1
          have c_eq_block : c = block :=
          part_insert.disjoint c c_in_family block block_in_family (
              Finset.nonempty_iff_ne_empty.mp
                ⟨y, Finset.mem_inter.mpr ⟨y_in_c, y_in_block⟩⟩
            )
          exact c_ne_block c_eq_block
      ·
        intro ⟨y_in_S, y_not_in_s⟩
        have y_in_union : y ∈ part_insert.family.biUnion id := by
          rw [part_insert.covers, Finset.mem_insert]
          right
          exact y_in_S
        rw [Finset.mem_biUnion] at y_in_union
        obtain ⟨c, c_in_family, y_in_c⟩ := y_in_union
        have c_in_rest : c ∈ rest_family := by
          rw [Finset.mem_sdiff]
          constructor
          · exact c_in_family
          ·
            rw [Finset.mem_singleton]
            intro c_eq_block
            subst c_eq_block
            have : y ∈ s := Finset.mem_inter.mpr ⟨y_in_c, y_in_S⟩
            exact y_not_in_s this
        use c, c_in_rest, y_in_c
    disjoint := by
      intros c hc d hd
      rw [Finset.mem_sdiff] at hc hd
      exact part_insert.disjoint c hc.1 d hd.1
  }

  exact ⟨⟨s, s_in_S_powerset⟩, rest_partition⟩

-- readme: see above, maybe this one should be called forward instead
def partition.insert_recurrence_backward
  {X: Type} [DecidableEq X]
  (S: Finset X)
  (x: X)
  (x_not_in_S: x ∉ S):
  (s : { x // x ∈ S.powerset }) × partition X (S \ ↑s) → partition X (insert x S) :=
by
  intro ⟨⟨s, s_in_S_powerset⟩, part_rest⟩
  let x_block := insert x s
  let insert_family := insert x_block part_rest.family

  have S_includes_s : s ⊆ S := Finset.mem_powerset.mp s_in_S_powerset
  have S_absorbs_s : S = s ∪ S := Finset.right_eq_union.mpr S_includes_s

  have part_rest_family: part_rest.family ⊆ (S \ s).powerset :=
  by
    rw [← Finset.mem_powerset]
    apply partition.family_in_double_powerset

  have x_block_disjoint_from_rest : x_block ∩ (S \ s) = ∅ :=
  by
    unfold x_block
    rw [
      Finset.insert_inter_of_not_mem,
      Finset.inter_sdiff_self,
    ]
    rw [Finset.mem_sdiff]
    exact fun h => x_not_in_S h.1

  -- this seems simplifiable...
  have x_block_disjoint_from_part_rest_family
    : ∀ a b, a = x_block → b ∈ part_rest.family → a ∩ b ≠ ∅ → False :=
  by
    intro a b a_eq_x_block b_in_rest ab_nonempty
    have b_subset : b ⊆ S \ s := Finset.mem_powerset.mp (part_rest_family b_in_rest)
    have disjoint : a ∩ b = ∅ :=
    by
      rw [a_eq_x_block, Finset.eq_empty_iff_forall_not_mem]
      intro y y_in_inter
      rw [Finset.mem_inter] at y_in_inter
      have y_in_S_sdiff_s : y ∈ S \ s := b_subset y_in_inter.2
      have : y ∈ x_block ∩ (S \ s) :=
        Finset.mem_inter.mpr ⟨y_in_inter.1, y_in_S_sdiff_s⟩
      rw [x_block_disjoint_from_rest] at this
      exact Finset.not_mem_empty y this
    exact ab_nonempty disjoint

  let part_insert: partition X (insert x S) := {
    family := insert_family,
    non_empty :=
    by
      intro c c_in_insert_family
      rw [Finset.mem_insert] at c_in_insert_family
      cases c_in_insert_family with
      | inl h =>
        rw [h]
        exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_insert_self x s⟩
      | inr h =>
        exact part_rest.non_empty c h
    covers :=
    by
      unfold insert_family
      rw [Finset.biUnion_insert]
      rw [id]
      rw [part_rest.covers]
      unfold x_block
      simp [Finset.union_insert]
      nth_rewrite 1 [← S_absorbs_s]
      rfl
    disjoint :=
    by
      unfold insert_family
      intros c c_in_insert_family d d_in_insert_family cd_not_disjoint
      rw [Finset.mem_insert] at c_in_insert_family d_in_insert_family
      cases c_in_insert_family with
      | inl c_is_x_block =>
        cases d_in_insert_family with
        | inl d_is_x_block => rw [c_is_x_block, d_is_x_block]
        | inr d_in_rest =>
          exfalso
          exact x_block_disjoint_from_part_rest_family c d c_is_x_block d_in_rest cd_not_disjoint
      | inr c_in_rest =>
        cases d_in_insert_family with
        | inl d_is_x_block =>
          exfalso
          exact x_block_disjoint_from_part_rest_family d c d_is_x_block c_in_rest (by rwa [Finset.inter_comm])
        | inr d_in_rest => exact part_rest.disjoint c c_in_rest d d_in_rest cd_not_disjoint
  }

  exact part_insert

lemma block_eq_insert_x_inter {X : Type} [DecidableEq X]
  (S : Finset X) (x : X) (block : Finset X)
  (x_in_block : x ∈ block)
  (block_subset : block ⊆ insert x S) :
  block = insert x (block ∩ S) := by
  ext y
  constructor
  · intro y_in_block
    by_cases h : y = x
    · rw [h]; exact Finset.mem_insert_self x _
    · -- y ≠ x and y ∈ block ⊆ insert x S, so y ∈ S
      have y_in_insert : y ∈ insert x S := block_subset y_in_block
      rw [Finset.mem_insert] at y_in_insert
      cases y_in_insert with
      | inl y_eq_x => exact absurd y_eq_x h
      | inr y_in_S =>
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_inter]
        exact ⟨y_in_block, y_in_S⟩
  · intro y_in_rhs
    rw [Finset.mem_insert] at y_in_rhs
    cases y_in_rhs with
    | inl y_eq_x => rw [y_eq_x]; exact x_in_block
    | inr y_in_inter => exact (Finset.mem_inter.mp y_in_inter).left

lemma insert_inter_eq {X : Type} [DecidableEq X]
  (S s : Finset X) (x : X)
  (x_not_in_S : x ∉ S)
  (s_subset : s ⊆ S) :
  (insert x s) ∩ S = s := by
  ext y
  constructor
  · intro y_in_inter
    obtain ⟨y_in_insert, y_in_S⟩ := Finset.mem_inter.mp y_in_inter
    rw [Finset.mem_insert] at y_in_insert
    cases y_in_insert with
    | inl y_eq_x =>
      rw [y_eq_x] at y_in_S
      exact absurd y_in_S x_not_in_S
    | inr y_in_s => exact y_in_s
  · intro y_in_s
    rw [Finset.mem_inter]
    constructor
    · exact Finset.mem_insert_of_mem y_in_s
    · exact s_subset y_in_s


def partition.insert_recurrence
  {X: Type} [DecidableEq X]
  (S: Finset X)
  (x: X)
  (x_not_in_S: x ∉ S):
  partition X (insert x S) ≃ Σ (s : S.powerset), partition X (S \ s) :=
{
  toFun := partition.insert_recurrence_forward S x x_not_in_S,

  invFun := partition.insert_recurrence_backward S x x_not_in_S,

  left_inv := by
    intro part_insert
    ext

    let blocks_with_x := part_insert.family.filter (fun b => x ∈ b)
    have exactly_one : ∃! block, block ∈ part_insert.family ∧ x ∈ block := sorry -- from uniqueness
    obtain ⟨block, ⟨block_in_family, x_in_block⟩, block_unique⟩ := exactly_one

    let s := block ∩ S

    have block_eq : block = insert x s := by
      have block_subset : block ⊆ insert x S := by
        intro y y_in_block
        have y_in_union : y ∈ part_insert.family.biUnion id :=
          Finset.mem_biUnion.mpr ⟨block, block_in_family, y_in_block⟩
        rwa [part_insert.covers] at y_in_union
      exact block_eq_insert_x_inter S x block x_in_block block_subset

    have family_eq : insert (insert x s) (part_insert.family \ {block}) = part_insert.family := by
      rw [
        ← block_eq,
        Finset.insert_eq,
        Finset.union_sdiff_self_eq_union,
        Finset.union_eq_right,
        Finset.singleton_subset_iff
      ]
      exact block_in_family


    exact this



  right_inv := sorry
}

lemma partition.forward_subset_family
  (X: Type) [DecidableEq X]
  (S: Finset X)
  (s: { x // x ∈ S.powerset })
  (x: X)
  (part_insert: partition X (insert x S))
  (x_not_in_S: x ∉ S):
  (partition.insert_recurrence_forward S x x_not_in_S part_insert).2.family ⊆ S.powerset :=
by
  intro c c_in_family
