## ai prompt etc

- teach ai my naming conventions (not using h*_) for propositions
- instruct them to not use tactic mode for trivial shit (term mode instead)
- instruct it to use apply and exact when possible to avoid rw and simp


## language server

### rename symbol didn't work
```
          obtain ⟨hc_in_family, c_nin_singleton_block⟩ := Finset.mem_sdiff.mp c_in_rest
          have c_ne_block : c ≠ block := Finset.not_mem_singleton.mp c_nin_singleton_block
          constructor
          ·
            have y_in_union : y ∈ part_insert.family.biUnion id := by
              rw [Finset.mem_biUnion]
              exact ⟨c, hc_in_family, y_in_c⟩
            rw [part_insert.covers] at y_in_union

            cases Finset.mem_insert.mp y_in_union with
            | inl h =>
              -- y = x, but x ∈ block and c ≠ block, contradiction
              subst h
              have : c = block := part_insert.disjoint c hc_in_family block block_in_family
                (by
                  rw [← Finset.nonempty_iff_ne_empty, Finset.Nonempty]
                  use y
                  rw [Finset.mem_inter]
                  exact ⟨y_in_c, x_in_block⟩)

              exact absurd this c_ne_block
            | inr h => exact h

          ·
```

if I renamed `hc_in_family` to `c_in_family` it wouldn't update `c = block := part_insert.disjoint c hc_in_family block block_in_family`

