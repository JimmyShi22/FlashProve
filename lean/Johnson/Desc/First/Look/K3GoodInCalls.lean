-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3GoodInCalls.lean: THE CLOSING STEP OF A LOOKUP's CHAIN AT ANY CALLER
(Johnson/Desc/First/Look/K3GoodInCaller.lean), AT K3.block's OWN TEXT AT THE SEAT ON A LINK's CALLS,
with one premise on the written rounds; and what every caller on the calls shares. After
k3_att_goodIn_any (Johnson/Desc/First/Look/K3AttRounds.lean), whose proof it is with the caller a
letter. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Main names:
  `foOk_of_shape`, `lm_of_planes`, `rounds_of_same`: three facts on public data that attention's
    caller had at AttOK, at any place's parameters.
  `ownIs_calls`: a yes of K3.block's decide at the calls' seat keeps "the record's own five are
    D's".
  `cfSig_stays`, `pinSig_back`: the two sentences on the first chain's oracle messages, over a
    stretch in front of which all their trees were sent, where the samples' reader has not turned.
  `k3_goodIn_calls`: THE END THEOREM at any caller r whose record of numbers is what the place's own
    parameters make, at any block b whose decide says yes only where K3.block's does, at a piece
    that holds "below b".
  `k3_calls_err`: each written round's error is at most 2^-157 of that round's challenge values.

Limits. Those of K3GoodInCaller.lean: the caller, Cond, Pin, Says and the readers are letters, with
laws.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3GoodInCaller
import Johnson.Desc.First.Look.K3AttRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- The record that a place's own parameters make passes the library's test on the numbers. -/
theorem foOk_of_shape {P0 : Desc.First.Look.P} {h : Forest.Shape} (hs : P0.shape = some h) :
    FoNums.ok h = true := by
  obtain ⟨h₀, a, b, e⟩ := shape_made hs
  rw [e]
  exact Cb.Fo.shape_ok a b

/-- A yes of the program's own test on the planes' packing is the two bounds. -/
theorem lm_of_planes {fs : Forest.Shape} {lm : ℕ}
    (h : (Forest.planeCols fs lm).toBool = true) : 5 ≤ lm ∧ lm ≤ fs.kT + 5 := by
  unfold Forest.planeCols at h
  split at h
  · simp [Except.toBool] at h
  · rename_i hn
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hn
    exact hn

/-- **The three premises on the written rounds, from one**, at any place's parameters. -/
theorem rounds_of_same {P0 : Desc.First.Look.P} {h : Forest.Shape} (hs : P0.shape = some h)
    (hN : 1 < h.NC) (hr : P0.entries.isSome = true) (ds : List RDT)
    (hR : List.Forall₂ SameAs ds P0.rounds) :
    (∀ d ∈ ds, Plain (toRD d)) ∧ (∀ d ∈ ds, NoAns d.items) ∧
      ds.map (·.entry) = P0.rounds.map (·.entry) := by
  have hE := entries_forEnts hs (foOk_of_shape hs) hN hr
  have hok : ∀ r ∈ P0.rounds, EntPlain r.entry := fun r hr' =>
    entPlain_forEnts _ _ _ (by
      rw [← hE]
      exact List.mem_map.2 ⟨r, hr', rfl⟩)
  exact ⟨same_all hR hok, fun d hd => (same_all hR hok d hd).noAns, same_entries hR⟩

/-- A yes of K3.block's decide at the calls' seat keeps the record's own five. -/
theorem ownIs_calls {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (P0 : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (D : Desc.First.Look.Sent) (link : ℕ)
    (s s' : Desc.First.S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before P0 guests).decide s rs cols =
      .ok s') (hO : OwnIs D link s) : OwnIs D link s' := by
  obtain ⟨F, y, -, hn, -, rfl⟩ := decide_ok _ piece laid before _ guests s s' rs cols h
  exact (ownOf_putCalls claim s y.1 y.2 hn).trans hO

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (D : Desc.First.Look.Sent)
  (l : List (OracleShape × ℕ)) (seatT : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin l.length) → Option ((Johnson.Pack.sigOf D.codes l).om i).Smp)
  (base : ℕ) (ds : List RDT) (hseat : ∀ i, (seatT i).1 < base) (s s' : S) (y : Fr.E.Str)
  (τ : Tr (uLT (ckP .two) ds)) (hs' : smp s' = smp s)
include hseat hs'

/-- "No oracle message has a collision at its sample's seed" stays over the stretch. -/
theorem cfSig_stays (h : CfSig G D.codes l seatT smp (fun _ => True) s (strsOf Fr y)) :
    CfSig G D.codes l seatT smp (fun _ => True) s'
      (strsOf Fr (behind (ckP .two) Fr base ds y τ)) :=
  fun i _ =>
    (pinStays (Cells := Unit) (Tok := Unit) G D.codes l seatT smp (fun _ _ => 0)
      (ckP .two) Fr base ds s' y τ ⟨(), (), fun _ _ _ _ => 0, fun _ _ _ _ _ => 0⟩ i (hseat i)).2.2
      (by
        have h0 := h i trivial
        unfold CfAt at h0 ⊢
        rw [hs']
        exact h0)

/-- "Every oracle message decodes to the witness's" goes back over the stretch. -/
theorem pinSig_back (w : Desc.Wit Cells Tok MsgT)
    (h : PinSig G D.codes l seatT smp arr (fun _ => True) s'
      (strsOf Fr (behind (ckP .two) Fr base ds y τ)) w) :
    PinSig G D.codes l seatT smp arr (fun _ => True) s (strsOf Fr y) w :=
  ⟨h.1, fun i _ => by
    have h0 := (pinStays G D.codes l seatT smp arr (ckP .two) Fr base ds
      s' y τ w i (hseat i)).1.1 (h.2 i trivial)
    unfold PinAt at h0 ⊢
    rw [hs'] at h0
    exact h0⟩

end

section
variable {Cl W : Type} {Fr : Frame} {r : LookupCRCaller} {set : Params.Setting}
  {x : Desc.First.Look.Place} {mk : ℕ → r.c.J₀} {pl : ℕ → ℕ → r.c.J₀}
  {st : Desc.First.S × Fr.E.Str → r.c.St₀} {y₀ : r.c.Ex.Str}
  {sm : Desc.First.S × Fr.E.Str → r.c.Sg.Smp}
  {wd : Desc.First.S × Fr.E.Str → r.c.Sg.ext.Str} {wt : W → r.c.Sg.Wit × r.c.Wp}
  {Cond : Desc.First.S × Fr.E.Str → Prop} {Pin : Desc.First.S × Fr.E.Str → W → Prop}
  {Says : Desc.First.S × Fr.E.Str → W → Prop}

/-- **THE END THEOREM AT ANY CALLER, AT ANY BLOCK WHOSE decide SAYS YES ONLY WHERE K3.block's DOES
AT THE CALLS' SEAT.** -/
theorem k3_goodIn_calls (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl W) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hselL : SelLookupCR [r])
    (hsh : (Desc.First.Look.P.ofPlace set false x).shape = some r.c.h) (hN : 1 < r.c.h.NC)
    (hp : (Forest.planeCols r.c.h x.lm).toBool = true)
    (hmk : ∀ t, r.c.L.mkS t = mk (x.F.next + t))
    (hbc : ∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h x.lm (t, k, j)).1 (FoNums.cellRC r.c.h x.lm (t, k, j)).2)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [r]).ε r) = some p.err)
    (hSt : ∀ s y (τ : Tr (uLT (ckP .two) p.ds)) rs cols s', b.decide s rs cols = .ok s' →
      st (s', behind (ckP .two) Fr p.base p.ds y τ) = st (s, y))
    (hOn : ∀ a, Cond a → ((kLookupCRN [r]).toKind.src r).on (cRd r st y₀ sm wd a))
    (hStay : ∀ s y (τ : Tr (uLT (ckP .two) p.ds)) rs cols s', b.decide s rs cols = .ok s' →
      Cond (s, y) → Cond (s', behind (ckP .two) Fr p.base p.ds y τ))
    (hBack : ∀ s y (τ : Tr (uLT (ckP .two) p.ds)) rs cols s' w, b.decide s rs cols = .ok s' →
      Pin (s', behind (ckP .two) Fr p.base p.ds y τ) w → Pin (s, y) w)
    (hDecs : ∀ a w, Pin a w → ∀ i, r.c.Sg.decs (sm a) (wd a) i = some ((wt w).1 i).1)
    (hOutB : ∀ X w, (forA Cb.Gl.E r.c.h r.c.L).lk.out id id X (zext (cMu r wt w)) →
      r.tgt (cMs r wt w) (X, y₀) →
        ((kLookupCRN [r]).B r).relR (X, y₀) (cMs r wt w, (wt w).2))
    (hSays : ∀ a w, ((kLookupCRN [r]).A r).relR (st a, y₀) (cMs r wt w, (wt w).2) → Says a w) :
    p.GoodIn (COn (Desc.K3.seatCalls claim).fork Cond)
      (COn' r x.lm x.F.next (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard Cond)
      (CFront Pin Says)
      (CBehind r x.lm x.F.next mk pl st wt (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard Pin) := by
  have hok := foOk_of_shape hsh
  have hv : 1 ≤ r.c.h.v := by
    rw [Cb.Fo.ok_v hok]
    omega
  have hRd := rounds_of_same hsh hN hr p.ds hR
  exact k3_goodIn_caller p hselL hok (lm_of_planes hp).1 (lm_of_planes hp).2 hmk hbc b.decide
    hext (meets_declared hsh hv hN hr p.ds hRd.1 hRd.2.2) hRd.2.1 hε
    (fun a τ a' h => piece_hears_below p _ hb hback a τ a' h)
    (Desc.First.Look.P.ofPlace set false x) hsh
    (fun K _ ρ lm s s' rs cols hw h =>
      k3DecideHears_calls claim piece laid before _ guests K ρ lm s s' rs cols hw
        (hyes s rs cols s' h))
    (fun s rs cols s' Fk h hF =>
      decide_first _ piece laid before _ guests s s' rs cols Fk hF (hyes s rs cols s' h))
    hSt hOn hStay hBack hDecs hOutB hSays

/-- **The end theorem's errors, as a number.** -/
theorem k3_calls_err (p : Piece (ckP .two) Fr Desc.First.S Cl W)
    (hsh : (Desc.First.Look.P.ofPlace set false x).shape = some r.c.h) (hN : 1 < r.c.h.NC)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [r]).ε r) = some p.err) :
    Iop.Err.Below p.err ((2 : ENNReal)⁻¹ ^ 157) :=
  lookupC_written (callersCR [r]) (okL_of_ok (foOk_of_shape hsh)) r.c (List.mem_singleton.2 rfl) _
    p.ds
    (rounds_of_same hsh hN hr p.ds hR).1
    ((rounds_of_same hsh hN hr p.ds hR).2.2.trans
      (entries_forEnts hsh (foOk_of_shape hsh) hN hr)) p.err hε

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rounds_of_same
#print axioms VerifiableInference.OnPublicFiles.ownIs_calls
#print axioms VerifiableInference.OnPublicFiles.cfSig_stays
#print axioms VerifiableInference.OnPublicFiles.pinSig_back
#print axioms VerifiableInference.OnPublicFiles.k3_goodIn_calls
#print axioms VerifiableInference.OnPublicFiles.k3_calls_err
