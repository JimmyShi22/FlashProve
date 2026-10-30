-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsClose.lean: K9's OWN SUB-PROTOCOLS AND K10's CLOSING.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM LooksClose.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksClose
import Johnson.Desc.First.Link.Law.LooksRuns
import Johnson.Desc.First.Link.Law.SlotsRuns
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.First.LedgerLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open VerifiableInference.Desc.K9L

theorem addSlot_size {w : E} {ns : ℕ} {a b : Array E} {x : ℕ × E} (h : K9.addSlot w ns a x = .ok b)
    :
    b.size = a.size := by
  unfold K9.addSlot at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  simp

theorem addForm_slots {F G : Fork} {w : E} {a : Aff} (h : addForm F w a = .ok G) :
    sl G = sl F := by
  unfold addForm at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  obtain ⟨LS, h2, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h2
  show (F.ns, LS.size) = (F.ns, F.LS.size)
  rw [foldE_inv (K9.addSlot w F.ns) (fun t => t.size = F.LS.size)
    (fun _ _ _ e hb => (addSlot_size e).trans hb) _ _ _ h2 rfl]

theorem addRuns_slots {F G : Fork} {w : E} {runs : Array Run2} (h : addRuns F w runs = .ok G) :
    sl G = sl F := by
  unfold addRuns at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rfl

theorem addOne_slots {F G : Fork} {cl : Claim} (h : addOne F cl = .ok G) :
    sl G = sl F := by
  unfold addOne at h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨G₁, h1, h⟩ := ok_bind h
  have e0 : sl x.2 = sl F := by
    unfold weightNext at hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    rw [← Except.ok.inj hx]
    rfl
  rw [addRuns_slots h, addForm_slots h1, e0]

/-- **The adding of a list of claims leaves the two numbers: no premise on the sizes.** -/
theorem addList_slots {F G : Fork} {cls : List Claim} (h : addList F cls = .ok G) :
    sl G = sl F :=
  foldE_inv addOne (fun H => sl H = sl F)
    (fun _ _ _ e hb => (addOne_slots e).trans hb) cls F G h rfl

section
variable (nsOf : ℕ → ℕ × ℕ)

/-- The lens's writing of a part. -/
theorem keeps_setS {s : S} {q p : K9.Part} (hq : atS.get? s = some q) (el : p.L.link = q.L.link)
    (ef : sl p.F = sl q.F) : KeepsSlots nsOf s (atS.set s p) := by
  have hL := (part_reads s q hq).1
  have hF := fork_part s q hq
  exact fun hs G L hG hL' => keeps_putsS nsOf hL hF (u := s) hL hF el ef hs G L hG hL'

/-- The batching draw. -/
theorem draw_decidesS {Cl : Type} (p : Where) :
    Decides (KeepsSlots nsOf) (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := ok_bind h
    obtain ⟨chi, _, h⟩ := ok_bind h
    obtain ⟨o, ho, h⟩ := ok_bind h
    obtain rfl := Except.ok.inj h
    exact keeps_setS nsOf (there_ok hq) (drawn_link _ _ _ _ _ _ _ ho)
      (sameSlots_of fun sh => slots_draw _ _ _ _ _ _ _ ho)
  · exact nomatch h

/-- Claims made and added. -/
theorem adds_decidesS {Cl : Type} (p : Where) (piece : ℕ) (what : String)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (KeepsSlots nsOf) claims) :
    Decides (KeepsSlots nsOf) (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨q, hq, h⟩ := ok_bind h
  obtain ⟨F, hF, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact keeps_transS nsOf _ _ _ (hcl s x hx)
    (keeps_setS nsOf (there_ok hq) rfl (addList_slots hF))

/-- **The batching.** -/
theorem batch_wholeS (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl (KeepsSlots nsOf) claims) : Whole (KeepsSlots nsOf) (batch atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := ok_bind h
  exact keeps_transS nsOf _ _ _ (draw_decidesS nsOf p s rs gs t₁ h1)
    (adds_decidesS nsOf p p.piece "the segment's" hcl t₁ [] [] s' h)

/-- The one equation: the ledger is marked as shut. -/
theorem oneEq_decidesS {Cl : Type} (p : Where) :
    Decides (KeepsSlots nsOf) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := ok_bind h
  obtain ⟨o, ho, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  have e : o.L = q.L ∧ sl o.F = sl q.F := by
    unfold door at ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨x, hx, ho⟩ := ok_bind ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨y, _, ho⟩ := ok_bind ho
    obtain ⟨d', _, ho⟩ := ok_bind ho
    rw [← Except.ok.inj ho]
    refine ⟨rfl, ?_⟩
    unfold equation at hx
    dsimp only at hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    rw [← Except.ok.inj hx]
    rfl
  exact keeps_setS nsOf (there_ok hq) (by show o.L.link = q.L.link; rw [e.1])
    (by show sl o.F = sl q.F; rw [e.2])

/-- A writing of the live state of the calls. -/
theorem keeps_putLiveS (s : S) (c : ChainCheck) : KeepsSlots nsOf s (s.putLive c) := by
  unfold S.putLive
  split
  case h_2 => exact keeps_sameS nsOf rfl rfl
  case h_1 L e =>
    refine keeps_sameS nsOf (First.fork_putLink s _) ?_
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x =>
      by_cases ho : x.opened = true
      · have e' : x.L = L := by simpa [S.link?, ho] using e
        simp [S.putLink, S.link?, ho, e']
      · simp [S.link?, ho] at e
    | lay x =>
      have e' : x.L = L := Option.some.inj e
      show some L.link = some x.L.link
      rw [e']
    | att x =>
      have e' : x.L = L := Option.some.inj e
      show some L.link = some x.L.link
      rw [e']
    | _ => exact nomatch e

/-- The closing (K10). -/
theorem closing_decidesS {Cl : Type} (P : First.Close.Par) :
    Decides (KeepsSlots nsOf) (closing (Cl := Cl) P) := by
  intro s rs gs s' h
  obtain ⟨r, _, rfl⟩ := Keeps.emap_ok h
  exact fun hs G L hG hL => keeps_putLiveS nsOf s { s.live with frame := r.frame } hs G L hG hL

/-- The shutting. -/
theorem shut_decidesS {Cl : Type} (p : Where) (piece : ℕ) :
    Decides (KeepsSlots nsOf) (shut (Cl := Cl) p piece) := by
  intro s rs gs s' h
  obtain ⟨L, hL, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  have hl := there_ok hL
  refine keeps_sameS nsOf (First.fork_putLink s _) ?_
  have k := (rb_putLink s L (closed L L.check.frame) hl rfl).num
  exact k

/-- **What closes a segment, sub-protocol by sub-protocol.** -/
theorem closeOf_wholeS {Cl : Type} (p : Where) (P : First.Close.Par) :
    ∀ b ∈ closeOf (Cl := Cl) p P, Whole (KeepsSlots nsOf) b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEq_decidesS (Cl := Cl) nsOf p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨closing_decidesS nsOf P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨shut_decidesS nsOf p _, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

end

end VerifiableInference.Desc.LinkJoin
