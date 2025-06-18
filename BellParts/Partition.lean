import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Algebra.Basic

variable
  {X: Type} [DecidableEq X]
  {S: Finset X}

-- from data.setoid.partitions
-- youtu.be/FEKsZj3WkTY
@[ext] structure partition (S: Finset X) where
  family : Finset (Finset X)
  non_empty: ∀ c ∈ family, c ≠ ∅
  covers: family.biUnion id = S
  -- TODO: consider refactoring this to
  -- disjoint: ∀ c ∈ family, ∀ d ∈ family, c ≠ d → Disjoint c d
  disjoint: ∀ c ∈ family, ∀ d ∈ family, c ∩ d ≠ ∅ → c = d

lemma partition.blocks_with_common_element_equal
  {b1 b2: Finset X}
  (part: partition S)
  (b1_in: b1 ∈ part.family)
  (b2_in: b2 ∈ part.family)
  {x: X}
  (x_in_b1: x ∈ b1)
  (x_in_b2: x ∈ b2) :
  b1 = b2 :=
by
  have blocks_intersect : b1 ∩ b2 ≠ ∅ :=
  by
    rw [← Finset.nonempty_iff_ne_empty]
    use x
    rw [Finset.mem_inter]
    exact ⟨x_in_b1, x_in_b2⟩
  exact part.disjoint b1 b1_in b2 b2_in blocks_intersect

lemma partition.block_subset_of_support
  { block: Finset X }
  (part: partition S)
  (block_in: block ∈ part.family) :
  block ⊆ S :=
by
  rw [← part.covers]
  exact Finset.subset_biUnion_of_mem id block_in

def partition.mk_if_valid (S: Finset X) (family: Finset (Finset X)) : Option (partition S) :=
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
  (fam: Finset (Finset X))
  (part: partition S)
  (mk_is_some: partition.mk_if_valid S fam = some part):
  part.family = fam :=
by
  unfold partition.mk_if_valid at mk_is_some
  split_ifs at mk_is_some with h₁ h₂ h₃; simp only [Option.some_inj] at mk_is_some
  rw [← mk_is_some]


lemma partition.mk_if_valid_inj_some  :
  ∀ (a a' : Finset (Finset X)),
  ∀ b ∈ mk_if_valid S a,
  b ∈ mk_if_valid S a' → a = a' :=
by
  intros fam1 fam2 p p_in_fam1 p_in_fam2
  rw [Option.mem_def] at p_in_fam1 p_in_fam2

  have fam_eq_fam1 : p.family = fam1 :=
    partition.mk_if_valid_id_family fam1 p p_in_fam1
  have fam_eq_fam2 : p.family = fam2 :=
    partition.mk_if_valid_id_family fam2 p p_in_fam2

  rw [← fam_eq_fam1, fam_eq_fam2]

lemma partition.family_in_double_powerset
 (part: partition S) : part.family ∈ (S.powerset.powerset) :=
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
  (part : partition S):
  part ∈ (S.powerset.powerset).filterMap
    (partition.mk_if_valid S)
    (partition.mk_if_valid_inj_some) :=
by
  simp_rw [Finset.mem_filterMap]
  use part.family
  constructor
  ·
    rw [Finset.mem_powerset]
    intro c c_in_fam
    rw [Finset.mem_powerset]
    intro x x_in_c
    have x_in_union : x ∈ part.family.biUnion id := by
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
instance partition.Fintype: Fintype (partition S) where
  elems := (S.powerset.powerset).filterMap
    (partition.mk_if_valid S)
    (partition.mk_if_valid_inj_some)
  complete :=
  by
    intro part
    exact partition.in_double_powerset_filterMap_mk_if_valid part

def finset_partition_count (S : Finset X): ℕ :=
  Fintype.card (partition S)

def the_empty_partition : partition (∅: Finset X) := {
  family := ∅,
  non_empty := fun c hc => (Finset.not_mem_empty c hc).elim
  covers := Finset.biUnion_empty
  disjoint := fun c hc => (Finset.not_mem_empty c hc).elim
}

lemma singleton_empty_powerset: ({∅}: (Finset (Finset X))).powerset = {∅, {∅}} := by
  ext fam
  constructor
  · intro h
    exact h
  · intro h
    exact h

lemma partitions_of_empty:
  Finset.filterMap
    (partition.mk_if_valid ∅)
    ({∅, {∅}}: (Finset (Finset (Finset X))))
    (partition.mk_if_valid_inj_some)
  =  {the_empty_partition} :=
by
  ext part
  simp only [Finset.mem_filterMap, Finset.mem_singleton, iff_def]
  constructor
  · intro h
    rcases h with ⟨fam, fam_in_set, part_eq⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at fam_in_set
    rcases fam_in_set with (fam_eq | fam_eq_singleton)
    ·
      rw [fam_eq] at part_eq
      unfold partition.mk_if_valid at part_eq
      simp only [Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, Finset.biUnion_empty, if_true] at part_eq
      injection part_eq with p_eq
      exact p_eq.symm
    ·
      rw [fam_eq_singleton] at part_eq
      unfold partition.mk_if_valid at part_eq
      -- kinda ugly to have to state this triviality
      have h_fail : ¬(∀ c ∈ ({∅} : Finset (Finset X)), c ≠ ∅) :=
        fun h => (h ∅ (Finset.mem_singleton_self ∅)) rfl

      simp only [h_fail, if_false] at part_eq
      contradiction
  ·
    intro h
    rw [h]
    use ∅
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    · unfold partition.mk_if_valid
      simp
      rfl

lemma partition.parts_of_empty_but_better
  (part: partition (∅: Finset X)) :
  part = the_empty_partition :=
by
  have h1 : part ∈ (∅ : Finset X).powerset.powerset.filterMap
    (partition.mk_if_valid ∅)
    (partition.mk_if_valid_inj_some) :=
    partition.in_double_powerset_filterMap_mk_if_valid part

  have h2 : (∅ : Finset X).powerset = {∅} := Finset.powerset_empty
  have h3 : ({∅} : Finset (Finset X)).powerset = {∅, {∅}} := singleton_empty_powerset
  rw [h2, h3] at h1
  rw [partitions_of_empty] at h1
  exact Finset.mem_singleton.mp h1

lemma card_partitions_of_empty:
  Fintype.card (partition (∅: Finset X)) = 1 :=
by
  unfold Fintype.card
  unfold Finset.univ
  unfold Fintype.elems
  unfold partition.Fintype
  simp only [Finset.powerset_empty]
  rw [singleton_empty_powerset, partitions_of_empty]
  unfold the_empty_partition
  rw [Finset.card_singleton]

-- readme: I'm sure this along other results should probably already be
-- present on mathlib and I could use them when I simplify to using
-- Setoid.IsPartition or Finpartition
-- todo: give a more mathy name to this (preimage filter whatever whatever)
lemma partition.element_in_exactly_one_block
  {x: X}
  (x_in_S: x ∈ S)
  (part: partition S):
    { b ∈ part.family | x ∈ b }.card = 1
  :=
by
  rw [Finset.card_eq_one]
  have x_in_union: x ∈ part.family.biUnion id := by rw [part.covers]; exact x_in_S
  simp only [Finset.mem_biUnion, id] at x_in_union
  obtain ⟨block, block_in_family, x_in_block⟩ := x_in_union
  use block
  ext b
  rw [Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨b_in_family, x_in_b⟩ := Finset.mem_filter.mp h
    exact partition.blocks_with_common_element_equal part b_in_family block_in_family x_in_b x_in_block
  · intro b_eq_block
    subst b_eq_block
    rw [Finset.mem_filter]
    exact ⟨block_in_family, x_in_block⟩

def partition.choose_eq_class

  (part: partition S)
  (x: X)
  (x_in_S: x ∈ S):
  { b // b ∈ part.family ∧ x ∈ b } :=
by
  let blocks_with_x := part.family.filter (fun b => x ∈ b)
  let block := blocks_with_x.biUnion id

  have one_block_with_x : blocks_with_x.card = 1 :=
    partition.element_in_exactly_one_block x_in_S part

  -- could use element_in_exactly_one_block here?
  have : blocks_with_x = {block} :=
  by
    rw [Finset.card_eq_one] at one_block_with_x
    obtain ⟨unique_block, blocks_singleton⟩ := one_block_with_x
    have : block = unique_block :=
    by
      unfold block
      rw [blocks_singleton, Finset.singleton_biUnion, id_eq]
    rw [← this] at blocks_singleton
    exact blocks_singleton

  have : block ∈ blocks_with_x := by simp [Finset.mem_singleton, this]

  rw [Finset.mem_filter] at this
  constructor
  . exact this

-- TODO: find this on mathlib
lemma disjoint_union_to_sdiff
  { s t r : Finset X }
  (s_disjoint_t : Disjoint s t):
    s ∪ t = r → t = r \ s
  :=
by
  intro union_eq
  ext x
  rw [Finset.mem_sdiff]
  constructor
  · intro hx
    constructor
    · rw [← union_eq]
      exact Finset.mem_union_right s hx
    · exact Finset.disjoint_right.mp s_disjoint_t hx
  · intro ⟨hxr, hxns⟩
    rw [← union_eq] at hxr
    cases Finset.mem_union.mp hxr with
    | inl h => exact absurd h hxns
    | inr h => exact h

structure ForwardResult
  {x: X}
  (x_not_in_S: x ∉ S)
  (part_insert: partition (insert x S))
where
  subset : { x // x ∈ S.powerset }
  part_rest : partition (S \ ↑subset)
  family_eq : part_insert.family = insert (insert x ↑subset) part_rest.family

-- readme: it's only called forward because of the direction
-- we defined the bijection but it definitely feels more backwards
def partition.insert_recurrence_forward

  {x: X}
  (x_not_in_S: x ∉ S):
    (part_insert: partition (insert x S)) ->
    ForwardResult x_not_in_S part_insert
  :=
by
  intro part_insert

  have ⟨block, ⟨block_in_family, x_in_block⟩⟩ :=
    partition.choose_eq_class part_insert x (Finset.mem_insert_self x S)

  let s := block ∩ S
  let rest_family := part_insert.family \ {block}

  have block_eq : block = insert x s :=
  by
    have block_subset : block ⊆ insert x S := by
      intro y y_in_block
      have y_in_union : y ∈ part_insert.family.biUnion id :=
        Finset.mem_biUnion.mpr ⟨block, block_in_family, y_in_block⟩
      rwa [part_insert.covers] at y_in_union
    rw [Finset.insert_inter_distrib, Finset.insert_eq_of_mem]
    exact (Finset.inter_eq_left.mpr block_subset).symm
    exact x_in_block

  -- todo: I also feel like this should shorter...
  have family_eq : part_insert.family = insert block (part_insert.family \ {block}) :=
  by
    simp only [
      Finset.insert_eq,
      Finset.union_sdiff_self_eq_union,
      Finset.right_eq_union,
      Finset.singleton_subset_iff,
    ]
    exact block_in_family

  -- this is cute but I hope it can be simplified
  have block_disjoint_rest : Disjoint block (rest_family.biUnion id) :=
  by
    unfold rest_family
    rw [Finset.disjoint_biUnion_right]
    simp [Finset.mem_sdiff, Finset.mem_singleton]
    intro c c_in_part_insert c_neq_block
    by_contra c_block_not_disjoint
    rw [Finset.disjoint_iff_inter_eq_empty] at c_block_not_disjoint
    let c_eq_block := part_insert.disjoint
      block block_in_family
      c c_in_part_insert
      c_block_not_disjoint
    apply c_neq_block
    rw [c_eq_block]

  let rest_partition : partition (S \ s) := {
    family := rest_family

    non_empty := by
      intros c hc
      rw [Finset.mem_sdiff] at hc
      exact part_insert.non_empty c hc.1

    covers := by
      rw [
        Finset.sdiff_inter_distrib_right,
        Finset.sdiff_self,
        Finset.union_empty
      ]
      have insert_covers
        : part_insert.family.biUnion id = insert x S := part_insert.covers
      rw [
        family_eq,
        Finset.biUnion_insert,
        id_eq
      ] at insert_covers
      apply disjoint_union_to_sdiff block_disjoint_rest at insert_covers
      rw [insert_covers]
      apply Finset.insert_sdiff_of_mem S x_in_block

    disjoint := by
      intros c hc d hd
      rw [Finset.mem_sdiff] at hc hd
      exact part_insert.disjoint c hc.1 d hd.1
  }

  exact {
    subset := ⟨s, Finset.mem_powerset.mpr Finset.inter_subset_right⟩,
    part_rest := rest_partition,
    family_eq := by rw [← block_eq]; exact family_eq
  }

structure BackwardResult
  (x: X)
  (s: { x // x ∈ S.powerset })
  (part_rest: partition (S \ s))
where
  part_insert : partition (insert x S)
  family_eq : part_insert.family = insert (insert x ↑s) part_rest.family

-- readme: see above, maybe this one should be called forward instead
def partition.insert_recurrence_backward
  {x: X}
  (x_not_in_S: x ∉ S):
    (s: { x // x ∈ S.powerset }) ->
    (part_rest: partition (S \ s)) ->
    BackwardResult x s part_rest
  :=
by
  intro ⟨s, s_in_S_powerset⟩
  intro part_rest
  let block := insert x s
  let insert_family := insert block part_rest.family

  have S_includes_s : s ⊆ S := Finset.mem_powerset.mp s_in_S_powerset
  have S_absorbs_s : S = s ∪ S := Finset.right_eq_union.mpr S_includes_s

  have part_rest_family: part_rest.family ⊆ (S \ s).powerset :=
  by
    rw [← Finset.mem_powerset]
    apply partition.family_in_double_powerset

  -- this proof is more or less duplicated on the bijection inv_right
  have disjoint_block_rest : block ∩ (S \ s) = ∅ :=
  by
    unfold block
    rw [
      Finset.insert_inter_of_not_mem,
      Finset.inter_sdiff_self,
    ]
    -- FIXME: if you collapse these rw's it doesn't work
    -- because it introduces two goals
    rw [Finset.mem_sdiff]
    exact fun h => x_not_in_S h.1
  -- TODO: consider using Disjoint more often
  apply Finset.disjoint_iff_inter_eq_empty.mpr at disjoint_block_rest

  have disjoint_block_rest_block : ∀ b ∈ part_rest.family, block ∩ b = ∅ :=
  by
    intro b b_in_rest
    rw [← Finset.disjoint_iff_inter_eq_empty]
    have b_subset : b ⊆ S \ s := Finset.mem_powerset.mp (part_rest_family b_in_rest)
    exact Finset.disjoint_of_subset_right b_subset disjoint_block_rest

  let part_insert: partition (insert x S) := {
    family := insert_family,

    non_empty :=
    by
      intro c c_in_insert_family
      rw [Finset.mem_insert] at c_in_insert_family
      cases c_in_insert_family with
      | inl h =>
        rw [h]
        exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_insert_self x s⟩
      | inr h => exact part_rest.non_empty c h

    covers :=
    by
      unfold insert_family
      rw [Finset.biUnion_insert, id, part_rest.covers]
      unfold block
      simp [Finset.union_insert]
      rw [← S_absorbs_s]

    disjoint :=
    by
      unfold insert_family
      intros c c_in d d_in hne
      rw [Finset.mem_insert] at c_in d_in
      match c_in, d_in with
        | Or.inl c_eq, Or.inl d_eq => rw [c_eq, d_eq]
        | Or.inl c_eq, Or.inr d_in_rest =>
          rw [c_eq] at hne
          exact absurd (disjoint_block_rest_block d d_in_rest) hne
        | Or.inr c_in_rest, Or.inl d_eq =>
          rw [d_eq] at hne
          rw [Finset.inter_comm] at hne
          exact absurd (disjoint_block_rest_block c c_in_rest) hne
        | Or.inr c_in_rest, Or.inr d_in_rest =>
          exact part_rest.disjoint c c_in_rest d d_in_rest hne
  }

  exact {
    part_insert := part_insert,
    family_eq := rfl
  }

lemma partition.forward_backward_subset_eq
  {x : X}
  (x_not_in_S : x ∉ S)
  (s : { x // x ∈ S.powerset })
  (part_rest : partition (S \ ↑s)) :
    let backward := insert_recurrence_backward x_not_in_S s part_rest
    let forward := insert_recurrence_forward x_not_in_S backward.part_insert
    forward.subset = s
  :=
by
  intro backward
  intro forward
  apply Subtype.eq

  have this1: backward.part_insert.family = insert (insert x ↑s) part_rest.family :=
    backward.family_eq

  have this2: backward.part_insert.family = insert (insert x ↑forward.subset) forward.part_rest.family :=
    forward.family_eq

  rw [this1] at this2

  have block_in_family :
    insert x (forward.subset: Finset X) ∈ backward.part_insert.family :=
  by
    have family_eq : backward.part_insert.family = insert (insert x ↑forward.subset) forward.part_rest.family :=
      forward.family_eq
    rw [family_eq]
    simp

  have block_eq : insert x (s : Finset X) = insert x (forward.subset : Finset X) :=
  by
    have s_block_in : insert x ↑s ∈ backward.part_insert.family :=
    by
      rw [backward.family_eq]
      exact Finset.mem_insert_self _ _

    have forward_block_in : insert x ↑forward.subset ∈ backward.part_insert.family :=
      block_in_family

    have x_in_s_block : x ∈ insert x (s : Finset X) := Finset.mem_insert_self _ _
    have x_in_forward_block : x ∈ insert x (forward.subset: Finset X) := Finset.mem_insert_self _ _

    exact partition.blocks_with_common_element_equal
      backward.part_insert s_block_in forward_block_in x_in_s_block x_in_forward_block
  rw [block_eq] at this2

  have x_not_in_s : x ∉ (s: Finset X) := by
    intro x_in_s
    have s_subset : ↑s ⊆ S := Finset.mem_powerset.mp s.property
    exact x_not_in_S (s_subset x_in_s)

  have x_not_in_forward : x ∉ (forward.subset: Finset X) :=
  by
    intro x_in_forward
    have forward_subset : ↑forward.subset ⊆ S := Finset.mem_powerset.mp forward.subset.property
    exact x_not_in_S (forward_subset x_in_forward)

  ext b
  have h := Finset.ext_iff.mp block_eq b
  simp only [Finset.mem_insert] at h
  by_cases b_eq_x : b = x
  ·
    subst b_eq_x
    simp [x_not_in_s, x_not_in_forward]
  ·
    simp only [b_eq_x, or_false] at h
    simp at h
    rw [h]

-- can't figure out how to get rid of this
-- maybe I have to define equality of partitions to only depend on families?
-- maybe instead of covers I could have a computed property `support` defined
-- as the biUnion id of the family
lemma partition.heq_of_family_eq
  {S1 S2 : Finset X}
  (p1 : partition S1) (p2 : partition S2)
  (equal_families : p1.family = p2.family) :
  HEq p1 p2 :=
by
  have equal_sets : S1 = S2 := by rw [← p1.covers, ← p2.covers, equal_families]
  subst equal_sets
  apply heq_of_eq
  ext
  simp only [equal_families]

def partition.insert_recurrence
  (x: X)
  (x_not_in_S: x ∉ S):
  partition (insert x S) ≃ Σ (s : S.powerset), partition (S \ s) :=
{
  toFun := fun part_insert =>
    let forward_result :=
      partition.insert_recurrence_forward x_not_in_S part_insert
    ⟨
      forward_result.subset,
      forward_result.part_rest
    ⟩

  invFun := fun (⟨subset, part⟩) =>
    let backward_result :=
      partition.insert_recurrence_backward x_not_in_S subset part
    backward_result.part_insert

  left_inv :=
  by
    intro part_insert
    simp only []

    let forward_result := insert_recurrence_forward x_not_in_S part_insert
    let backward_result := insert_recurrence_backward x_not_in_S
      forward_result.subset forward_result.part_rest

    ext
    rw [backward_result.family_eq]
    rw [forward_result.family_eq]

  right_inv :=
  by
    intro ⟨s, part_rest⟩
    simp only []

    let x_in_block := Finset.mem_insert_self x ↑s

    let backward_result := insert_recurrence_backward x_not_in_S s part_rest
    let forward_result := insert_recurrence_forward x_not_in_S backward_result.part_insert

    have forward_subset_eq_s : forward_result.subset = s :=
      forward_backward_subset_eq x_not_in_S s part_rest

    -- todo: parsing was bugged with ⊈
    have block_nin_rest : ¬insert x ↑s ⊆ S \ ↑s :=
    by
      intro block_in_rest
      rw [Finset.insert_subset_iff, Finset.mem_sdiff] at block_in_rest
      simp only [x_not_in_S, false_and] at block_in_rest

    have block_nin_part_rest : insert x ↑s ∉ part_rest.family :=
    by
      intro h
      exact absurd (partition.block_subset_of_support part_rest h) block_nin_rest

    have block_nin_forward : insert x ↑s ∉ forward_result.part_rest.family :=
    by
      intro h
      have block_in_rest : insert x ↑s ⊆ S \ ↑s :=
      by
        simp only [← forward_subset_eq_s] at h ⊢
        exact partition.block_subset_of_support forward_result.part_rest h
      exact absurd block_in_rest block_nin_rest

    have part_rest_eq : forward_result.part_rest.family = part_rest.family :=
    by
      let forward_fam := forward_result.family_eq

      rw [backward_result.family_eq] at forward_fam
      simp [forward_subset_eq_s] at forward_fam
      -- todo: should this be shorter somehow? looks like it could be
      ext block
      have fams_eq := Finset.ext_iff.mp forward_fam block
      simp only [Finset.mem_insert] at fams_eq
      by_cases block_eq : block = insert x ↑s
      · simp only [block_eq, block_nin_part_rest, block_nin_forward]
      · simp only [block_eq, or_false, false_or] at fams_eq
        exact fams_eq.symm

    -- TODO: this can probably be removed by defining equality differently for
    -- partitions
    rw [Sigma.mk.inj_iff]
    constructor
    · exact forward_subset_eq_s
    . exact partition.heq_of_family_eq
        forward_result.part_rest
        part_rest
        part_rest_eq
}

-- I would have expected something like this to be decidable
-- from existing theorems in mathlib, but I'm not sure
-- but it's chill it's simple enough
-- TODO: use powersetCard instead
def sigma_powerset_by_card :
  (Σ s : { x // x ∈ S.powerset }, partition (S \ ↑s))
  ≃
  (Σ m : Fin (S.card + 1), Σ s : { x // x ∈ S.powerset ∧ x.card = m }, partition (S \ ↑s))
:= {
  toFun :=
  by
    rintro ⟨s_hs, part_rest⟩
    obtain ⟨s, s_in_powerset⟩ := s_hs
    have : s.card ≤ S.card := (Finset.card_le_card (Finset.mem_powerset.mp s_in_powerset))
    have : s.card < S.card + 1 := Nat.lt_add_one_of_le this
    let m := Fin.mk s.card this
    exact ⟨m, ⟨⟨s, ⟨s_in_powerset, by simp only [m]⟩⟩, part_rest⟩⟩

  invFun := λ ⟨m, ⟨⟨s, s_in_powerset, s_card⟩, p⟩⟩ => ⟨⟨s, s_in_powerset⟩, p⟩,

  left_inv := by intro; simp,

  right_inv :=
  by
    intro ⟨m, ⟨⟨s, s_in_powerset, s_card⟩, p⟩⟩
    simp only [Function.comp_apply]
    have : s.card ≤ S.card := (Finset.card_le_card (Finset.mem_powerset.mp s_in_powerset))
    have s_card_bound : s.card < S.card + 1 := Nat.lt_succ_of_le this
    have : (⟨s.card, s_card_bound⟩ : Fin (S.card + 1)) = m := by ext; simp only; exact s_card
    -- todo: can I reduce this?
    congr 3
    · rw [s_card]
    · rw [s_card]
    . rw [s_card]
    . simp [this, s_card]
}

-- TODO: I think I now know how to not need this anymore
def powersetCard_as_predicate
  (m: Fin (S.card + 1)):
  { x // x ∈ S.powerset ∧ x.card = m } ≃ { x // x ∈ S.powersetCard m }
:= {
  toFun := by
    intro x
    conv =>
      arg 1
      ext x
      rw [Finset.mem_powersetCard]
      rw [← Finset.mem_powerset]
    exact x
  invFun := by
    intro x
    conv at x =>
      arg 1
      ext x
      rw [Finset.mem_powersetCard]
      rw [← Finset.mem_powerset]
    exact x
  left_inv := by intro; simp
  right_inv := by intro; simp
}
