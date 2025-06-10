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

lemma partitions_of_empty {X: Type} [DecidableEq X] :
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

structure ForwardResult
  (X: Type) [DecidableEq X]
  (S: Finset X)
  (x: X)
  (x_not_in_S: x ∉ S)
  (part_insert: partition X (insert x S))
where
  subset : { x // x ∈ S.powerset }
  part_rest : partition X (S \ ↑subset)
  family_eq : part_insert.family = insert (insert x ↑subset) part_rest.family

-- readme: it's only called forward because of the direction
-- we defined the bijection but it definitely feels more backwards
def partition.insert_recurrence_forward
  {X: Type} [DecidableEq X]
  (S: Finset X)
  (x: X)
  (x_not_in_S: x ∉ S):
    (part_insert: partition X (insert x S)) ->
    ForwardResult X S x x_not_in_S part_insert
  :=
by
  intro part_insert
  have x_in_insert: x ∈ (insert x S) := Finset.mem_insert_self x S
  have x_in_union : x ∈ part_insert.family.biUnion id :=
  by
    rw [part_insert.covers]
    exact x_in_insert
  rw [Finset.mem_biUnion] at x_in_union

  let blocks_with_x := part_insert.family.filter (fun b => x ∈ b)
  let block := blocks_with_x.biUnion id

  -- TODO: these two next hypothesis should be combined into one
  -- and simplified a lot
  have exactly_one_x_block : blocks_with_x.card = 1 :=
  by
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

  have ⟨block_in_family, x_in_block⟩:
    block ∈ part_insert.family ∧ x ∈ block :=
  by
    rw [Finset.card_eq_one] at exactly_one_x_block
    obtain ⟨unique_block, blocks_singleton⟩ := exactly_one_x_block
    have : block = unique_block :=
    by
      unfold block
      simp [blocks_singleton, Finset.biUnion_singleton, id]
    rw [this]
    have : unique_block ∈ blocks_with_x := by rw [blocks_singleton, Finset.mem_singleton]
    rw [Finset.mem_filter] at this
    exact this

  let s := block ∩ S
  have s_subset : s ⊆ S := Finset.inter_subset_right
  have s_in_S_powerset: s ∈ S.powerset := Finset.mem_powerset.mpr s_subset

  have part_insert_in_double_powerset :
    part_insert.family ∈ (insert x S).powerset.powerset
  :=
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
    -- intuitively this should be easier too
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

  have block_eq : block = insert x s :=
  by
    have block_subset : block ⊆ insert x S := by
      intro y y_in_block
      have y_in_union : y ∈ part_insert.family.biUnion id :=
        Finset.mem_biUnion.mpr ⟨block, block_in_family, y_in_block⟩
      rwa [part_insert.covers] at y_in_union
    simp only [s, block]
    rw [Finset.insert_inter_distrib, Finset.insert_eq_of_mem]
    exact (Finset.inter_eq_left.mpr block_subset).symm
    exact x_in_block

  have family_eq : part_insert.family = insert (insert x s) rest_family :=
  by
    rw [← block_eq]
    unfold rest_family
    simp only [
      Finset.insert_eq,
      Finset.union_sdiff_self_eq_union,
      Finset.right_eq_union,
      Finset.singleton_subset_iff,
      block,
      s
    ]
    exact block_in_family

  exact {
    subset := ⟨s, s_in_S_powerset⟩,
    part_rest := rest_partition,
    family_eq := family_eq
  }

structure BackwardResult
  (X: Type) [DecidableEq X]
  (S: Finset X)
  (x: X)
  (s: { x // x ∈ S.powerset })
  (part_rest: partition X (S \ s))
where
  part_insert : partition X (insert x S)
  family_eq : part_insert.family = insert (insert x ↑s) part_rest.family

-- readme: see above, maybe this one should be called forward instead
def partition.insert_recurrence_backward
  {X: Type} [DecidableEq X]
  (S: Finset X)
  (x: X)
  (x_not_in_S: x ∉ S):
    (s: { x // x ∈ S.powerset }) ->
    (part_rest: partition X (S \ s)) ->
    BackwardResult X S x s part_rest
  :=
by
  intro ⟨s, s_in_S_powerset⟩
  intro part_rest
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
      rw [← S_absorbs_s]
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

  have family_eq : part_insert.family = insert (insert x s) part_rest.family :=
  by
    simp [part_insert]
    unfold insert_family
    unfold x_block
    rfl

  exact {
    part_insert := part_insert,
    family_eq := family_eq
  }

lemma partition.forward_backward_subset_eq {X : Type} [DecidableEq X]
  (S : Finset X) (x : X) (x_not_in_S : x ∉ S)
  (s : { x // x ∈ S.powerset })
  (part_rest : partition X (S \ ↑s)) :
    let backward := insert_recurrence_backward S x x_not_in_S s part_rest
    let forward := insert_recurrence_forward S x x_not_in_S backward.part_insert
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

    exact backward.part_insert.disjoint _ s_block_in _ forward_block_in
      (by
        rw [← Finset.nonempty_iff_ne_empty];
        use x;
        rw [Finset.mem_inter]
        exact ⟨x_in_s_block, x_in_forward_block⟩
      )
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
lemma partition.heq_of_family_eq {X : Type} [DecidableEq X]
  {S1 S2 : Finset X}
  (p1 : partition X S1) (p2 : partition X S2)
  (equal_families : p1.family = p2.family) :
  HEq p1 p2 :=
by
  have equal_sets : S1 = S2 := by rw [← p1.covers, ← p2.covers, equal_families]
  subst equal_sets
  apply heq_of_eq
  ext
  simp only [equal_families]


def partition.insert_recurrence
  {X: Type} [DecidableEq X]
  (S: Finset X)
  (x: X)
  (x_not_in_S: x ∉ S):
  partition X (insert x S) ≃ Σ (s : S.powerset), partition X (S \ s) :=
{
  toFun := fun part_insert =>
    let forward_result :=
      partition.insert_recurrence_forward S x x_not_in_S part_insert
    ⟨
      forward_result.subset,
      forward_result.part_rest
    ⟩

  invFun := fun (⟨subset, part⟩) =>
    let backward_result :=
      partition.insert_recurrence_backward S x x_not_in_S subset part
    backward_result.part_insert

  left_inv :=
  by
    intro part_insert
    simp only []

    let forward_result := insert_recurrence_forward S x x_not_in_S part_insert
    let backward_result := insert_recurrence_backward S x x_not_in_S
      forward_result.subset forward_result.part_rest

    ext
    rw [backward_result.family_eq]
    rw [forward_result.family_eq]

  right_inv :=
  by
    intro ⟨s, part_rest⟩
    simp only []

    let backward_result := insert_recurrence_backward S x x_not_in_S s part_rest
    let forward_result := insert_recurrence_forward S x x_not_in_S backward_result.part_insert

    have forward_subset_eq_s : forward_result.subset = s :=
      forward_backward_subset_eq S x x_not_in_S s part_rest

    have x_in_block : x ∈ insert x (s: Finset X) := Finset.mem_insert_self x ↑s

    have not_in_part_rest : insert x ↑s ∉ part_rest.family :=
    by
      intro h
      -- TODO: dedup this proof from not_in_forward
      have block_subset : insert x ↑s ⊆ S \ ↑s :=
      by
        have family_in_powerset := partition.family_in_double_powerset (S \ ↑s) part_rest
        rw [Finset.mem_powerset] at family_in_powerset
        have : insert x ↑s ∈ (S \ ↑s).powerset := family_in_powerset h
        exact Finset.mem_powerset.mp this
      have : x ∈ S \ ↑s := block_subset x_in_block
      have : x ∈ S := (Finset.mem_sdiff.mp this).1
      exact x_not_in_S this

    have not_in_forward : insert x ↑s ∉ forward_result.part_rest.family :=
    by
      intro h
      have block_subset : insert x ↑s ⊆ S \ ↑s :=
      by
        simp [← forward_subset_eq_s] at h ⊢
        have := partition.family_in_double_powerset (S \ ↑forward_result.subset) forward_result.part_rest
        exact Finset.mem_powerset.mp (Finset.mem_powerset.mp this h)
      have : x ∈ S \ ↑s := block_subset x_in_block
      have : x ∈ S := (Finset.mem_sdiff.mp (block_subset x_in_block)).1
      exact x_not_in_S this

    have part_rest_eq : forward_result.part_rest.family = part_rest.family :=
    by
      have forward_fam: backward_result.part_insert.family = (insert
        (insert x ↑forward_result.subset)
        forward_result.part_rest.family
      ) := forward_result.family_eq

      rw [backward_result.family_eq] at forward_fam
      simp [forward_subset_eq_s] at forward_fam

      ext a
      have h := Finset.ext_iff.mp forward_fam a
      simp only [Finset.mem_insert] at h
      by_cases ha : a = insert x ↑s
      ·
        rw [ha]
        simp [not_in_part_rest, not_in_forward]
      ·
        simp only [ha, or_false] at h
        simp at h
        exact h.symm

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
