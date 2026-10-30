-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/FrontFallList.lean: the smallness test's entry in the first chain's
list of falls: the test `k8Front` at each of the 25 batchings, and what a list that holds the entry
gives: where the list's fall is silent at the batching's place, at a state that holds the test's data
and at a challenge with one drawn element, no column on which a read lies has the weight 0
(`LiveCols`), which the kind's run at the batching asks. At an empty list of falls that silence says
nothing, which is why the entry must stand in the list that the acceptance at the batching is stated
at.

THIS ENTRY ALONE IS NOT THE KIND's WHOLE SHARE OF α. The falls' stated numbers count only at states
all of whose columns are live: at a column that is all 0 the test speaks at every batching element
(`k8Front_dead`, Honest/K8/FrontDead.lean). That event is the mark `P1K8.deadMark`
(Johnson/P1K8R/DeadMark.lean), at the kind's own round, which is counted apart. The kind's second fall,
`k8ShareFall`, at the member without a round, is not in this entry.

  `k8FrontFalls`     the 25 falls at the ground's own numbers
  `k8FrontFalls_mem`  the fall of segment l is a member
  `k8Front_of_silent`  **the cover**: at a list that holds a fall of this form, silence at its place
                    is silence of `k8Front`
  `k8Front_of_list`  the same at a list that holds the entry whole
  `k8Live_of_silent`   **the cover as it is spent**: `LiveCols` at the drawn element

Not here: any bound on how often the fall speaks; that its stated number is that bound; that a state
at the batching's border holds the test's data (the premise of `k8Live_of_silent`: the thread's to
give); that the numbers k8ColsAt and k8TauAt, which are 0 where a segment lacks, are the state's.
That the place stands in the description at number 14 l + 9, 347 at the head: `P1K8.batch_there`. Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Falls
import Johnson.Desc.ProofFile.Honest.K8.FallNumbers
import Johnson.Desc.ProofFile.Honest.K8.EqAllFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc.First (S)

/-- **The entry**: the first fall of each of the 25 segments, at the ground's own numbers. The number
o is 1 at the output head, which is segment 24, else 0. -/
def k8FrontFalls (G : ProofFile.Ground) : List (Fall S) :=
  (List.range 25).map fun l =>
    k8FrontFall l (if l = 24 then 1 else 0) (k8ColsAt G l) (k8TauAt G l)

/-- The fall of segment l is a member. -/
theorem k8FrontFalls_mem (G : ProofFile.Ground) {l : Nat} (hl : l < 25) :
    k8FrontFall l (if l = 24 then 1 else 0) (k8ColsAt G l) (k8TauAt G l) ∈ k8FrontFalls G :=
  List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩

/-- **The cover.** -/
theorem k8Front_of_silent {fs : List (Fall S)} {l o c t : Nat} (h : k8FrontFall l o c t ∈ fs)
    {s : S} {ds : List Fmt.Drawn} (hs : fallOf fs (batchPlace l o) s ds = none) :
    k8Front s ds = none := by
  unfold fallOf at hs
  exact List.findSome?_eq_none_iff.1 hs _
    (List.mem_filter.2 ⟨h, by simp [k8FrontFall]⟩)

/-- The same at a list that holds the entry. -/
theorem k8Front_of_list {fs : List (Fall S)} {G : ProofFile.Ground} (h : ∀ f ∈ k8FrontFalls G, f ∈ fs)
    {l : Nat} (hl : l < 25) {s : S} {ds : List Fmt.Drawn}
    (hs : fallOf fs (batchPlace l (if l = 24 then 1 else 0)) s ds = none) :
    k8Front s ds = none :=
  k8Front_of_silent (h _ (k8FrontFalls_mem G hl)) hs

/-- **The cover as it is spent.** At a state that holds the test's data, at a challenge with one drawn
element x, silence at the place gives `LiveCols` at that element, at every list of tables. -/
theorem k8Live_of_silent {fs : List (Fall S)} {l o c t : Nat} (h : k8FrontFall l o c t ∈ fs)
    {s : S} {d : Fmt.Drawn} (hs : fallOf fs (batchPlace l o) s [d] = none)
    {tl : OnBytes.Model.HTailF2} (ht : s.tl? = some tl) {x : Fmt.Ext} (hx : d.elems = [x])
    (funs : Array OnBytes.Model.HFun) :
    VerifiableInference.Desc.First.K8.Honest.LiveCols tl funs (OnBytes.E.ofTriple x) := by
  have h0 : k8Front s [d] = none := k8Front_of_silent h hs
  have e : k8Front s [d] = (zeroColumnWeight tl (OnBytes.E.ofTriple x)).map fun _ =>
      "the smallness test: a column of the drawn matrix has the weight 0" := by
    unfold k8Front
    simp only [ht, List.map_cons, List.map_nil, hx]
  rw [e] at h0
  exact liveCols_of_front tl funs _ (Option.map_eq_none_iff.1 h0)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Live_of_silent
#print axioms ProofFile.Honest.K8.k8FrontFalls
#print axioms ProofFile.Honest.K8.k8FrontFalls_mem
#print axioms ProofFile.Honest.K8.k8Front_of_silent
#print axioms ProofFile.Honest.K8.k8Front_of_list
