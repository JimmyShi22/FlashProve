-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Keeps.lean: K9's CLAUSE ON WHAT THE BATCHING's MEMBER LEAVES AND TURNS, WITH ITS
PAYER. A definition, statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.
  `K9Keeps p g s s'`   A CLOSED SENTENCE on the state in front of the member (s) and behind it (s'): s' bears no mark
      of failure · its reply is the reply in front · there are a challenge x, what draw and gatherer yield there (y)
      and a ledger G with `BatBehind p g s x y G s'` (Honest/K9/YesAtSeat.lean): HOW WHAT THE MEMBER TURNS HAS TURNED:
      s' is the state behind the gatherer with K9's part laid into it, whose ledger is what K9's adding made of the
      gathered claims
  **`k9Keeps_of_yes`**, **`k9Keeps_of_step`**   THE PAYER: of a segment of which `SeatedFree` holds
      (Honest/K9/AtSeatAll.lean): a yes of the seated block's decision, or of its step, at s with s' behind gives it:
      FROM THE YES ALONE
  **`K9Keeps.left`**   WHAT IS LEFT, DRAWN OFF THE CLAUSE BY WHOEVER NEEDS IT: at the frame's gatherer, for every
      relation R with the four premises of `left_of_behind` (Honest/K9/Leaves.lean): R s s'. No seat and no yes is
      spent: two fillers with unlike R draw each its own
  `K9Keeps.seven`, `K9Keeps.pins`   that, called: at `setLeaves` (seven fields of the state) and at `pinLeft O`: each
      under ONE premise: each run of the order keeps the relation
WHY WHAT IS LEFT IS NO FIELD OF THE CLAUSE: the member runs the OTHER kinds' runs of claims: what these leave of the
state is each kind's to say. FOR WHOEVER LAYS THE CLAUSE AS A TERM: p and the link Lk are pinned by `SeatedFree`'s own
fields (c.links[l]? = some Lk; the lot's reading of the public parameters at l gives p): they need not come out of an
∃. No member. `K9Keeps.left` is called by `K9Keeps.seven`, `K9Keeps.pins` and Honest/K9/KeepsPaid.lean;
`K9Keeps.seven` by that file; `K9Keeps.pins` and `k9Keeps_of_yes` by no line; `k9Keeps_of_step` by
Honest/K9/ThrBehind.lean, SeatTied.lean, XkBat.lean and KeepsAtPlace.lean.
WHAT IS NOT CLAIMED. The clause on R of any kind's run. That a pin reads no more than `pinLeft`
(Honest/K9/Leaves.lean's head says where that stands). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **K9's clause.** -/
structure K9Keeps (p : Desc.K9.Where) (g : S → Except String (List Claim × S)) (s s' : S) : Prop where
  mark : s'.failed = none
  reply : s'.out.reply = s.out.reply
  behind : ∃ x y G, BatBehind p g s x y G s'

/-- **What is left, drawn off the clause.** -/
theorem K9Keeps.left {p : Desc.K9.Where} {each : ℕ × String → List Claim → S → Except String Unit}
    {bs : List (Block S Claim)} {order : List (ℕ × String)} {s s' : S}
    (H : K9Keeps p (claimsInBy each bs order) s s') (R : S → S → Prop) (hrefl : ∀ u, R u u)
    (htrans : ∀ u v z, R u v → R v z → R u z)
    (hset : ∀ u a q, Desc.K9.atS.get? u = some a → q.d = a.d → R u (Desc.K9.atS.set u q))
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n u z, run n u = .ok z → R u z.2) : R s s' := by
  obtain ⟨x, y, G, hB⟩ := H.behind
  exact left_of_behind p each bs order R hrefl htrans hset hrun s s' x y G hB

/-- The seven fields, if each run of the order leaves them. -/
theorem K9Keeps.seven {p : Desc.K9.Where} {each : ℕ × String → List Claim → S → Except String Unit}
    {bs : List (Block S Claim)} {order : List (ℕ × String)} {s s' : S}
    (H : K9Keeps p (claimsInBy each bs order) s s')
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n u z, run n u = .ok z → setLeaves u z.2) :
    setLeaves s s' :=
  H.left setLeaves setLeaves.refl (fun _ _ _ h h' => h.trans h') set_leaves hrun

/-- The first sample rows of the messages in O, if each run of the order leaves them. -/
theorem K9Keeps.pins {p : Desc.K9.Where} {each : ℕ × String → List Claim → S → Except String Unit}
    {bs : List (Block S Claim)} {order : List (ℕ × String)} {s s' : S}
    (H : K9Keeps p (claimsInBy each bs order) s s') (O : List ℕ)
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n u z, run n u = .ok z → pinLeft O u z.2) :
    pinLeft O s s' :=
  H.left (pinLeft O) (fun _ _ _ => rfl) (fun _ _ _ h h' o ho => (h' o ho).trans (h o ho))
    (fun u a q ha hq => pinLeft_of_leaves O (set_leaves u a q ha hq)) hrun

variable {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
  {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **The payer, at the decision.** -/
theorem k9Keeps_of_yes (Sd : SeatedFree c Z l k Lk p w) (s s' : S) (x : E)
    (hd : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], drawnOne x⟩] [] = .ok s') :
    K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s' := by
  obtain ⟨y, G, hB, hf, ho⟩ := behind_of_yes Sd s s' x hd
  exact ⟨hf, ho, ⟨x, y, G, hB⟩⟩

/-- **The payer, at the step.** -/
theorem k9Keeps_of_step (Sd : SeatedFree c Z l k Lk p w) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (n : ℕ)
    (hy : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', n)) :
    K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s' := by
  obtain ⟨r, tr, _, _, _, y, G, hB, hf, ho⟩ := behind_of_step Sd ft s s' rs cols n hy
  exact ⟨hf, ho, ⟨_, y, G, hB⟩⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.K9Keeps.left
#print axioms ProofFile.Honest.K9.K9Keeps.seven
#print axioms ProofFile.Honest.K9.K9Keeps.pins
#print axioms ProofFile.Honest.K9.k9Keeps_of_yes
#print axioms ProofFile.Honest.K9.k9Keeps_of_step
#print axioms ProofFile.Honest.K9.K9Keeps
