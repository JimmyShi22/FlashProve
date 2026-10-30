-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadScan.lean: every value line of the parameter file holds a number below 2^32, so the
policy's three words are bounded as the library asks.

The library's theorem on a request under its policy asks that the policy's clip C is below 2^40
(AcceptancePolicy.OK, Inst/Model/ProgramRPol.lean). No test of the output head's layout gives that
(Johnson/Road/HeadPub.lean). It comes from the strict scan of the parameter file (polScan in
OnBytes/Model/Config.lean): the step that reads a value line refuses a number of 2^32 or more, and
no other step touches the values read so far.

How. The scan folds one step over the file's lines. "All values read so far are below 2^32" holds of
the empty state and is kept by each step: a value line is tested before its value is kept; the
optional lines and the call lines write other fields. The record of the value lines takes C from the
list of names and values by its name, and 0 if the name is missing.

Main theorems: callLine_vals, lineAfterF_vals (these steps leave the values); polStep_small;
foldlM_keeps; lookup_small; clip_of_scan; clip_of_public; polOK_of_public (AcceptancePolicy.OK of the policy's
words in what the public part of a stage returns).

What is not claimed. Nothing on the numbers that are made of two lines (they can reach 2^64), on the
frame's lines or on the optional lines. That the scan returns a value is a hypothesis. The program
does not import this file.
-/
import Johnson.Road.HeadPub
import OnBytes.Model.Config

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

/-- A call line leaves the values read so far. -/
theorem callLine_vals {prof : ℕ} {s r : Model.PolState} {line : List UInt8}
    (h : Model.callLine prof s line = .ok r) : r.vals = s.vals := by
  unfold Model.callLine at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := ok_of_bind h)
    | (split at h)
  all_goals first
    | (cases h
       rfl)
    | cases h

/-- A line behind the value lines leaves the values read so far. -/
theorem lineAfterF_vals {prof : ℕ} {afterTbl : Bool} {s r : Model.PolState} {line : List UInt8}
    (h : Model.lineAfterF prof afterTbl s line = .ok r) : r.vals = s.vals := by
  unfold Model.lineAfterF at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := ok_of_bind h)
    | (split at h)
  all_goals first
    | exact callLine_vals h
    | (cases h
       rfl)
    | cases h

/-- One step of the scan keeps "all values read so far are below 2^32". -/
theorem polStep_small {frame : Params.Lines} {prof : ℕ} {names : Array String}
    {s r : Model.PolState} {line : List UInt8}
    (h : Model.polStep frame prof names s line = .ok r)
    (hs : ∀ v ∈ s.vals.toList, v < 2 ^ 32) : ∀ v ∈ r.vals.toList, v < 2 ^ 32 := by
  unfold Model.polStep at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  dsimp only at h
  split at h
  · obtain ⟨sc, -, h⟩ := ok_of_bind h
    split at h
    · obtain ⟨_, t1, h⟩ := ok_of_bind h
      obtain ⟨-, -, h⟩ := ok_of_bind h
      obtain ⟨-, -, h⟩ := ok_of_bind h
      obtain ⟨_, h⟩ := ok_of_ite h
      cases h
      have hv := Nat.not_le.mp (of_decide_eq_false (false_of_refuseIf t1))
      intro v hm
      have hm' : v ∈ (s.vals.push _).toList := hm
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
      rcases hm' with k | k
      · exact hs v k
      · rw [k]
        exact hv
    · cases h
  · rw [lineAfterF_vals h]
    exact hs

/-- A fold whose steps keep a property keeps it. -/
theorem foldlM_keeps {σ β : Type} (f : σ → β → Except String σ) (I : σ → Prop)
    (step : ∀ s a s', I s → f s a = .ok s' → I s') :
    ∀ (l : List β) (s r : σ), I s → l.foldlM f s = .ok r → I r
  | [], s, r, hI, h => by
    rw [List.foldlM_nil] at h
    have e : s = r := Except.ok.inj h
    rw [← e]
    exact hI
  | a :: l, s, r, hI, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s', h1, h2⟩ := ok_of_bind h
    exact foldlM_keeps f I step l s' r (step s a s' hI h1) h2

/-- What a list of names and values holds under a name, or 0, is below every bound above 0 that is
above all values. -/
theorem lookup_small {B : ℕ} (hB : 0 < B) (n : String) : ∀ (names : List String) (vals : List ℕ),
    (∀ v ∈ vals, v < B) → ((names.zip vals).lookup n).getD 0 < B
  | [], _, _ => hB
  | _ :: _, [], _ => hB
  | n0 :: ns, v :: vs, h => by
    rw [List.zip_cons_cons, List.lookup_cons]
    split
    · exact h v List.mem_cons_self
    · exact lookup_small hB n ns vs fun w hw => h w (List.mem_cons_of_mem _ hw)

/-- **The clip that the strict scan returns is below 2^32.** -/
theorem clip_of_scan {pol : ByteArray} {P : Model.PolScan} (h : Model.polScan pol = .ok P) :
    P.h.clipC < 2 ^ 32 := by
  unfold Model.polScan at h
  dsimp only at h
  split at h
  · obtain ⟨⟨frame, rest⟩, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    split at h
    · obtain ⟨plt, -, h⟩ := ok_of_bind h
      obtain ⟨-, -, h⟩ := ok_of_bind h
      obtain ⟨s, hf, h⟩ := ok_of_bind h
      obtain ⟨-, -, h⟩ := ok_of_bind h
      obtain ⟨-, -, h⟩ := ok_of_bind h
      cases h
      have hs : ∀ v ∈ s.vals.toList, v < 2 ^ 32 :=
        foldlM_keeps _ (fun t : Model.PolState => ∀ v ∈ t.vals.toList, v < 2 ^ 32)
          (fun t a t' hI ht => polStep_small ht hI) _ _ _
          (fun v hv => by
            have hv' : v ∈ ([] : List ℕ) := hv
            cases hv') hf
      exact lookup_small (by norm_num) "C" _ _ hs
    · obtain ⟨_, k, -⟩ := ok_of_bind h
      cases k
  · obtain ⟨_, k, -⟩ := ok_of_bind h
    cases k

/-- **The clip in what the public part of a stage returns is below 2^32.** -/
theorem clip_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) : X.hS.clipC < 2 ^ 32 := by
  obtain ⟨P, y, hpl, -, -, eS, -⟩ := public_parts h
  unfold Model.Verify.polLayout at hpl
  obtain ⟨P0, hP, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨y0, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hpl
  rw [eS]
  exact clip_of_scan hP

/-- **The policy's three words are bounded as the library asks**, in what the public part of a stage
returns. -/
theorem polOK_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) :
    Inst.Model.AcceptancePolicy.OK ⟨X.hS.clipC, X.hS.theta, X.hS.cap⟩ := by
  obtain ⟨P, y, -, -, -, -, -, hl, -⟩ := public_parts h
  have hc := clip_of_public h
  exact polOK_of_policy (policy_of_layout hl) (by omega)

#print axioms clip_of_scan
#print axioms polOK_of_public

end OnBytes.Road.Hd
