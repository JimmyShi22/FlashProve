-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FirstSrc.lean: the bridge from the book's trees to the plan's declared openings
and their sources, at the first stage of the proximity test (the kind K12).

Johnson/Desc/K12/Law/FixedBefore.lean and Johnson/Desc/K12/Law/FixedLaw.lean hold the one statement
"every tree that a stage opens was sent in front of the first draw of the stage that spends it"
(Fixed, fixedOk, fixed_switch). Nothing of it is stated anew here. Statements and proofs.
Main names:
  `OpensAre`: the trees that the first switch opens (P.ts, in the book's order), each with its key
    and a source src t, are what the switch's declared rounds open, in turn. It is public: the plan
    against the book.
  `OpensAre.keys`: gives firstReads_keyed (Johnson/Desc/K12/Law/FirstRead.lean) its premise on the
    keys.
  `OpensAre.fixed`: what holds of every declared opening holds of every src t.
  `first_fixed`: under fixedOk p = true and OpensAre at the first switch's two declared rounds,
    every tree that FirstReads reads a word off has a source that is fixed in front of the first
    draw of the first stage's fold: it is named in p.before, or (at the one fold that sends its own
    mask) it is sent in that fold's first round.
Limits: No soundness is claimed, and nothing is said on hiding.
It does not say that g t (FirstReads' written columns of the tree at the place t) are the columns of
the message that src t names: an implication has no world of messages. Whoever spends the law in a
game lays g t as the written columns of the message src t, and o j and oF with them; then y and z
are functions of messages that first_fixed names, not of the test's own transcripts (but for the own
mask, which is the fold's first message's).
In first_fixed the quantifier over every shape is idle.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.FirstRead
import Johnson.Desc.K12.Law.FixedLaw

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.FixedBefore

/-- The trees P.ts, each with its key and the source src t, are what the declared rounds cut open,
in turn. -/
def OpensAre {s : Sg} {G : Gp s} (firstTree : ℕ) (cut : List Fmt.DeclaredRound) (P : GpData G)
    (src : ℕ → Fmt.TreeSource) : Prop :=
  (cut.flatMap (·.opens)).map (fun o => (o.1.tree - firstTree, o.2)) =
    P.ts.map fun t => (P.key t, src t)

theorem OpensAre.keys {s : Sg} {G : Gp s} {firstTree : ℕ} {cut : List Fmt.DeclaredRound}
    {P : GpData G} {src : ℕ → Fmt.TreeSource} (h : OpensAre firstTree cut P src) :
    (cut.flatMap fun r => r.opens.map fun o => o.1.tree - firstTree) = P.ts.map P.key := by
  have h1 := congrArg (List.map Prod.fst) h
  rw [List.map_map, List.map_map, List.map_flatMap] at h1
  exact h1

theorem OpensAre.fixed {s : Sg} {G : Gp s} {firstTree : ℕ} {cut : List Fmt.DeclaredRound}
    {P : GpData G} {src : ℕ → Fmt.TreeSource} (h : OpensAre firstTree cut P src)
    (Q : Fmt.TreeSource → Prop) (hQ : ∀ r ∈ cut, ∀ o ∈ r.opens, Q o.2) : ∀ t ∈ P.ts, Q (src t) := by
  intro t ht
  have h1 := congrArg (List.map Prod.snd) h
  rw [List.map_map, List.map_map] at h1
  have hm : src t ∈ (cut.flatMap (·.opens)).map (Prod.snd ∘ fun o => (o.1.tree - firstTree, o.2)) :=
      by
    rw [h1]
    exact List.mem_map.2 ⟨t, ht, rfl⟩
  obtain ⟨o, ho, e⟩ := List.mem_map.1 hm
  obtain ⟨r, hr, hor⟩ := List.mem_flatMap.1 ho
  rw [← e]
  exact hQ r hr o hor

/-- Every tree off which FirstReads reads a word has a source that is fixed in front of the first
stage's first draw. s0: the first stage. -/
theorem first_fixed (p : P12) (h : fixedOk p = true) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (s0 : Fmt.M1.Stage)
    (hj : 0 + 1 < p.nums.stages.length) (hs : p.nums.stages[0]? = some s0) {s : Sg} {G : Gp s}
    (P : GpData G) (src : ℕ → Fmt.TreeSource)
    (hO : OpensAre p.nums.firstTree
      ((rds.drop (foldStart 1 p.nums.stages 0 + 1 + s0.k)).take 2) P src) :
    ∀ t ∈ P.ts, ∀ sh : Fmt.Shape,
      Fixed p.place.chain p.before p.nums rds (foldStart 1 p.nums.stages 0 + 1) (sh, src t) :=
  fun t ht sh => hO.fixed
    (fun x => Fixed p.place.chain p.before p.nums rds (foldStart 1 p.nums.stages 0 + 1) (sh, x))
    (fun r hr' o ho => fixed_switch p h rds hr 0 s0 hj hs r hr' o ho) t ht

end H2K.Sw
