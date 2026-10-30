-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Over Block.lean, State.lean and the seats that go with them (Stored/HeadSeatAt.lean,
Stored/ReplySeatAt.lean). lookup_alike: the seat's lookup reads S.lookHeard?;
reads_alike: the proof follows the reader that refuses.

Johnson/Desc/Kinds/Law/RunsFixed.lean: FOR K9's PAYERS (RunOk, Johnson/Desc/First/Batch/Law/Gather.lean, in the form "up to PscRun.Later"): THE OUTPUT HEAD's OWN THREE RUNS OF CLAIMS ("norm" | "policy" | "logits") STATE THE SAME
LIST OF FORMS AT EVERY RECORD THAT GOES ON FROM ONE AT WHICH THEY RETURN: the list is fixed by what lies in front of the batching's draw.
  Alike s s'      s' goes on from s, AS FAR AS K6's READERS SEE: both stand in the head's link; what was heard (x, squaresP), the lookup's record (lookHeard), the tables of reads (t), "opened", the reply and the
                  request's words are the same; the ledger of s' is LATER than that of s (what lies under a filled slot stays), and the arrays' numbers of columns are the same. NOTHING IS ASKED of the
                  link's context L, of what is owed, used or laid, of the statement, or of the ledger's sums.
  allOf_later     the way back from the program's record to what the text heard (Johnson/Stored/HeadSeat.lean: allOf) returns the same at a later ledger.
  letters_alike   where lettersAt returns at s, it returns THE SAME LETTERS at s'.
  run_fixed       s0: a record at which the letters are read; s: any record that goes on from it: where one of the three runs returns at s: the record behind IS s; its claims are the run's forms AT s0's LETTERS; each
                  claim is plain (its own number's power of chi; no run of entries). MEANT FOR PlainOk (Johnson/Desc/First/Batch/Law/PlainRuns.lean; read, not imported): BY READING ALONE, from "the record behind
                  is s" its clauses on the part, the core, the arrays' frame, good and Fx follow, "more" by its own refl; the length is lens_K6; THE CLAUSE ON THE VALUES IS NOT MET HERE. The join is not typed.
  forms_length · lens_K6   the three lists have 29, 4 and 2 claims, at any letters.
WHAT IT IS NOT. NOT RunOk: K9's files' letters (Lens, Others, Fx9, wsumK, termsAt) are not imported. NOT the equation on the claims' values: for that: every slot that the forms name is filled in front of the draw (not
shown here; Law/Takes.lean has the stretch that the hearing fills) and the entries' values (the virtual rows' weights: "Fu" in other files). "join": Law/HeadRunsCarry.lean: k6_join; its one form is the lookup's.
Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Desc.Kinds.Law.HeardBack
import Johnson.Desc.Kinds.Law.K06Runs
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Kinds.Law.NormSquares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)

/-- s' goes on from s, as far as K6's readers see. -/
def Alike (s s' : S) : Prop :=
  ∃ o o', s.here = .head o ∧ s'.here = .head o' ∧ o'.x = o.x ∧ o'.squaresP = o.squaresP ∧
    o'.t = o.t ∧ o'.opened = o.opened ∧ o'.lookHeard = o.lookHeard ∧
    s'.out.reply = s.out.reply ∧ s'.req = s.req ∧ Later o.F o'.F ∧
    o'.F.trees.map (·.K) = o.F.trees.map (·.K)

theorem bind_mono {α β : Type} {a a' : Option α} {f f' : α → Option β}
    (ha : ∀ x, a = some x → a' = some x) (hf : ∀ x y, f x = some y → f' x = some y) {y : β}
    (e : (a >>= f) = some y) : (a' >>= f') = some y := by
  cases h : a with
  | none => rw [h] at e; cases e
  | some x =>
    rw [h] at e
    rw [ha x h]
    exact hf x y e

theorem sumOf_later {F G : Fork} (h : Later F G) (t : OnBytes.Model.Tsc) (r : Point) (n : Nat)
    (s : Sum) (e : sumOf F t r n = some s) : sumOf G t r n = some s := by
  unfold sumOf at e ⊢
  exact bind_mono (fun _ => hidAt_later h) (fun _ _ e1 =>
    bind_mono (fun _ => hidsAt_later h) (fun _ _ e2 => e2) e1) e

/-- **The way back returns the same at a later ledger.** -/
theorem allOf_later {F G : Fork} (h : Later F G) (x : OnBytes.Model.Head.Heard)
    (sq : Option Part.MaskedSum.Heard) (H : HeardAll) (e : allOf F x sq = some H) :
    allOf G x sq = some H := by
  unfold allOf at e ⊢
  exact bind_mono (fun _ => hidsAt_later h) (fun _ _ e1 =>
    bind_mono (fun _ => id) (fun _ _ e2 =>
    bind_mono (fun _ => hidAt_later h) (fun _ _ e3 =>
    bind_mono (fun _ => hidAt_later h) (fun _ _ e4 =>
    bind_mono (fun _ => hidsAt_later h) (fun _ _ e5 =>
    bind_mono (fun _ => id) (fun _ _ e6 =>
    bind_mono (fun _ => sumOf_later h _ _ _ _) (fun _ _ e7 =>
    bind_mono (fun _ => sumOf_later h _ _ _ _) (fun _ _ e8 =>
    bind_mono (fun _ => sumOf_later h _ _ _ _) (fun _ _ e9 => e9) e8) e7) e6) e5) e4) e3) e2) e1) e

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat)

theorem lookup_alike {s s' : S} (a : Alike s s') :
    (seatAt h iU3).lookup s' = (seatAt h iU3).lookup s := by
  obtain ⟨o, o', ho, ho', ex, _, _, eo, el, _⟩ := a
  have _ := ex
  show s'.lookHeard?.map _ = s.lookHeard?.map _
  unfold S.lookHeard?
  rw [ho, ho']
  simp only [eo, el]

theorem token_alike {s s' : S} (a : Alike s s') :
    Reply.token (seatAt h iU3).toSeat s' = Reply.token (seatAt h iU3).toSeat s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, er, _⟩ := a
  show (s'.out.reply).map _ = (s.out.reply).map _
  rw [er]

theorem request_alike {s s' : S} (a : Alike s s') :
    (seatAt h iU3).request s' = (seatAt h iU3).request s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, eq, _⟩ := a
  show requestOf s' = requestOf s
  unfold requestOf S.tokv S.rowR S.rowE S.reqT
  rw [eq]

theorem given_alike (p : Par) {s s' : S} (a : Alike s s') :
    given p (seatAt h iU3) s' = given p (seatAt h iU3) s := by
  unfold given
  rw [lookup_alike h iU3 a, token_alike h iU3 a, request_alike h iU3 a]

theorem heard_alike {s s' : S} (a : Alike s s') (H : HeardAll)
    (e : (seatAt h iU3).heard s = some H) : (seatAt h iU3).heard s' = some H := by
  obtain ⟨o, o', ho, ho', ex, es, _, _, _, _, _, hL, _⟩ := a
  have e' : (match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H := e
  show (match s'.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H
  rw [ho] at e'
  rw [ho']
  simp only [ex, es] at e' ⊢
  obtain ⟨q, hq, e1⟩ := Option.bind_eq_some_iff.mp e'
  obtain ⟨x, hx, e2⟩ := Option.bind_eq_some_iff.mp e1
  rw [hq, hx]
  exact allOf_later hL x _ H e2

theorem reads_alike {s s' : S} (a : Alike s s') :
    (seatAt h iU3).reads s' = (seatAt h iU3).reads s := by
  obtain ⟨o, o', ho, ho', _, _, et, eo, _, _, _, _, hK⟩ := a
  have hc : ((o'.F.trees[iU3]?).map (·.K)) = ((o.F.trees[iU3]?).map (·.K)) := by
    have e1 := congrArg (fun A => A[iU3]?) hK
    simpa using e1
  unfold seatAt
  simp only [S.fork?, ho, ho', eo, et]
  cases o.opened
  · rfl
  · simp only [if_true]
    rw [et]
    cases h1 : o'.F.trees[iU3]? with
    | none =>
      cases h2 : o.F.trees[iU3]? with
      | none => rfl
      | some b => rw [h1, h2] at hc; simp at hc
    | some a =>
      cases h2 : o.F.trees[iU3]? with
      | none => rw [h1, h2] at hc; simp at hc
      | some b =>
        rw [h1, h2] at hc
        have hk : a.K = b.K := by simpa using hc
        simp only [Option.bind_some, hk]

/-- **Where the letters are read at s, the same letters are read at s'.** -/
theorem letters_alike (p : Par) {s s' : S} (a : Alike s s') (v : Given × Behind × Places)
    (e : lettersAt p (seatAt h iU3) s = .ok v) : lettersAt p (seatAt h iU3) s' = .ok v := by
  unfold lettersAt at e ⊢
  rw [given_alike h iU3 p a, reads_alike h iU3 a]
  cases hg : given p (seatAt h iU3) s with
  | error m => rw [hg] at e; cases e
  | ok g =>
    rw [hg] at e
    cases hH : (seatAt h iU3).heard s with
    | none => rw [hH] at e; cases e
    | some H =>
      rw [hH] at e
      rw [heard_alike h iU3 a H hH]
      exact e

/-- **A RUN's CLAIMS ARE FIXED BY THE LETTERS IN FRONT.** s0: a record at which the letters are read (in front of the batching's draw); s: any record that goes on from it. Where one of K6's three runs
returns at s: the record behind is s; the claims are the run's forms AT s0's LETTERS, each a plain claim. -/
theorem run_fixed (p : Par) (l piece : Nat) (name : String)
    (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) {s0 s : S}
    (a : Alike s0 s) (v : Given × Behind × Places) (e0 : lettersAt p (seatAt h iU3) s0 = .ok v)
    (n : Nat) (c : List Claim) (s1 : S) (e : run n s = .ok (c, s1)) :
    s1 = s ∧ (∃ fs, ((fun (_ : Given) (_ : Behind) (_ : Places) => claims) v.1 v.2.1 v.2.2).lookup
      name = some fs ∧ c = fs.map asClaim) ∧ ∀ cl ∈ c, cl.eqFirst = none ∧ cl.runs = #[] := by
  obtain ⟨g, b, x, fs, h1, h2, h3⟩ := k6_run_spec asClaim (seatAt h iU3) l piece p name run n s s1 c
    hrun e
  have h4 := letters_alike h iU3 p a v e0
  rw [h1] at h4
  obtain rfl := Except.ok.inj h4
  refine ⟨k6_same h iU3 l piece p (name, run) (lookup_mem _ _ _ hrun) n s (c, s1) e,
    ⟨fs, h2, h3⟩, fun cl hcl => ?_⟩
  rw [h3] at hcl
  obtain ⟨f, _, rfl⟩ := List.mem_map.mp hcl
  exact ⟨rfl, rfl⟩

end At

/-! ## The lengths -/

section Lens

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard] [FinalNorm.Reads] [Reads]

theorem forms_length : (FinalNorm.forms).length = 29 := by
  have hlen : Norm.rowForms.length = 17 := by
    rw [rowForms_eq]
    simp [OnBytes.Desc.First.P6.carries_eq, OnBytes.Desc.First.P6.lines,
      OnBytes.Desc.First.P6.root_eq, OnBytes.Desc.First.P6.reciprocal_eq]
  unfold FinalNorm.forms Norm.forms
  rw [List.length_append, List.length_append, List.length_append, hlen, squareForms_eq,
    productForms_eq]
  rfl

/-- The number of claims of a run. -/
def lenK6 (name : String) : Nat :=
  if name == "norm" then 29 else if name == "policy" then 4 else if name == "logits" then 2 else 0

/-- **29, 4 and 2.** -/
theorem lens_K6 (name : String) (fs : List Form) (hl : claims.lookup name = some fs) :
    fs.length = lenK6 name := by
  unfold claims at hl
  unfold lenK6
  simp only [List.lookup_cons, List.lookup_nil] at hl
  by_cases h1 : name == "norm"
  · rw [h1] at hl
    rw [if_pos h1, ← Option.some.inj hl]
    exact forms_length
  · have h1' : (name == "norm") = false := by simpa using h1
    rw [h1'] at hl
    rw [if_neg h1]
    by_cases h2 : name == "policy"
    · rw [h2] at hl
      rw [if_pos h2, ← Option.some.inj hl]
      rfl
    · have h2' : (name == "policy") = false := by simpa using h2
      rw [h2'] at hl
      rw [if_neg h2]
      by_cases h3 : name == "logits"
      · rw [h3] at hl
        rw [if_pos h3, ← Option.some.inj hl]
        rfl
      · have h3' : (name == "logits") = false := by simpa using h3
        rw [h3'] at hl
        cases hl

end Lens

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.allOf_later
#print axioms VerifiableInference.Desc.Kinds.Head.Law.letters_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Law.run_fixed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.lens_K6
