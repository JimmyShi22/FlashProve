-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HandsPaid.lean: BENEATH THE LINK's NAMED LIST: THE SECOND AND THE THIRD
OF THE THREE HAND-ONS OF THE PROMISE THAT STAND INSIDE ITS FIELD A (`LinkOwes`: conds.h12,
conds.hon3; in LinkRest.lean: Ah12, Ahon3), EACH TO THE LETTER, from `h12_mgR` and `hon3_mgR`
(RidesAtMgR.lean) with what these take brought down. Theorems.

What is said.
  `quiet_nil`: a yes of a row of one quiet move adds no claim. `smpNamed_tri`: **the reader of the
    OOD samples by the message's fixed number answers alike at two states whose statements agree in
    each message's shape, mark and sample rows.** `total_behind`: **behind a yes of the piece that
    holds the frame's sub-protocol behind the batching the one sum can be taken**, from the list's
    own field htin and «that sub-protocol is a row of one quiet move». `oraQ_of`, `eqAsks_at`: what
    the riders on the oracles take over that piece and over the one equation's, from the fence's
    test on the plan and facts on the letters (as `oraB_of`, OraPaid.lean); at the one equation with
    the list's own field notIx. `ah12_of`: **the hand-on over the frame's sub-protocol behind the
    batching.** `ahon3_of`: **the hand-on over the one equation.**

Limits. BOOK-KEEPING OVER FOUR THEOREMS THAT LAY. What is left by name: Bools on the written list;
the two places' facts; the plan's two counts over the two places; the runs' share; «reached» is
handed on over the two pieces; the fence's test; the pieces' first trees; the two readers answer
alike (at the one equation: where the statements agree in each message's shape, mark and sample
rows); the rows' numbers fit (`rowsAtFit`); the group is the plan's; htin; notIx. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.OraPaid
import Johnson.Desc.First.Link.Law.OracleAsksEq
import Johnson.Desc.First.Link.Law.LinkList
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers fenceFit rowsAtFit)
open _root_.Run.PQ (CK)

/-- A yes of a row of one quiet move adds no claim. -/
theorem quiet_nil {T : Type} (X : K9.Lens T) (g : T → Except String T) (t t' : T)
    (cls : List Claim) (h : MovesYes X [.quiet g] t t' cls) : cls = [] := by
  obtain ⟨_, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩ := h
  rfl

/-- **THE READER OF THE OOD SAMPLES BY THE MESSAGE's FIXED NUMBER ANSWERS ALIKE AT TWO STATES WHOSE
STATEMENTS AGREE IN EACH MESSAGE's SHAPE, MARK AND SAMPLE ROWS**: it reads the first sample row. -/
theorem smpNamed_tri {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (a b : P × S)
    (h : SameBy tri a.2.st b.2.st) (s : Sending) (i : Fin s.l.length) :
    smpNamed cs seats b s i = smpNamed cs seats a s i := by
  refine smpNamed_stays cs seats a b s i ?_ ?_
  · unfold K1.formsAt
    exact bind_blind tri (fun y => (y.2.2[0]?).map _) _ _ (h.2 _)
  · unfold K1.ansAt
    exact bind_blind tri (fun y => (y.2.2[0]?).map _) _ _ (h.2 _)

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (links : List ModelPart) (pl : List Place) (z : P)
  (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz

/-- **BEHIND THE FRAME's SUB-PROTOCOL THE ONE SUM CAN BE TAKEN.** -/
theorem total_behind {α : Type} (L : Link S Claim)
    (movesQ : IsMoves atS [.quiet L.runBehind] L.behindB) (pq : Piece C F S Claim WT)
    (hpq : pq.b = below L.behindB)
    (htin : ∀ a t, onK k a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn (𝔇.N.group m) t = true) :
    ∀ a τ b, onK k a → pq.ior.red.out a τ = some b → K9.totalIn (𝔇.N.group m) b.1 = true := by
  intro a τ b ha hout
  obtain ⟨_, _, f3, _⟩ := piece_yes pq a b τ hout
  rw [hpq] at f3
  obtain ⟨cls, hy⟩ := movesQ.dec _ _ _ _ (below_yes _ _ _ _ _ f3).2
  obtain rfl := quiet_nil atS _ _ _ _ hy
  exact htin a b.1 ha hy

/-- What the riders on the oracles take over the frame's sub-protocol behind the batching. -/
theorem oraQ_of (hfen : fenceFit 𝔇.N links pl = true) (hk : k ≤ pl.length) (L : Link S Claim)
    (p : Where) (share : LinkShare L p) (pq : Piece C F S Claim WT) (hpq : pq.b = below L.behindB)
    (hb : 𝔇.N.treesAt pl[k]? ≤ pq.base)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (hs : ∀ s s' : S, s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s)) :
    ∀ a τ b, onK k a → pq.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k pq.base a.1 b.1 := by
  intro a τ b _ hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact oracleAsks_of 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k pq.base hfen hk hb
    (fun c s s' _ _ => hd c s s') (fun s s' e _ => hs s s' e) a.1 b.1
    (share.two.2 _ _ _ _ _ j hstep).1

/-- What the hand-on over the one equation asks of the parameters and the frame's numbering. -/
theorem eqAsks_at (hfen : fenceFit 𝔇.N links pl = true) (hk : k ≤ pl.length) (pw : Where)
    (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim WT) (hpe : pe.b = below b₃) (hb : 𝔇.N.treesAt pl[k]? ≤ pe.base)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (hsE : ∀ s s' : S, SameBy tri s.st s'.st → s'.book = s.book → 𝔇.smp (z, s') = 𝔇.smp (z, s))
    (notIx : ∀ a, onK k a → OwnNotIndex a.1) :
    ∀ a τ b, onK k a → pe.ior.red.out a τ = some b →
      EqAsks 𝔇 𝔇.N links pl z k pe.base a.1 b.1 := by
  intro a τ b ha hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact ⟨oracleAsks_eq 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k pe.base hfen hk hb hd hsE pw b₃ hb₃ _
    _ _ _ _ j hstep, notIx a ha⟩

/-- **THE HAND-ON OVER THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING** (k: that piece's border). -/
theorem ah12_of {α : Type} (hlf : linkFit links pl = true)
    (hp9 : pubFit9 true moreAll links pl = true) (p1 p2 : Place) (hp1 : pl[k]? = some p1)
    (hp2 : pl[k + 1]? = some p2) (hl : p1.link = some m) (hpc : p1.piece = hearN links m + 2)
    (ht : 𝔇.N.treesAt pl[k + 1]? = 𝔇.N.treesAt pl[k]?)
    (hm : 𝔇.N.msgsAt pl[k + 1]? = 𝔇.N.msgsAt pl[k]?) (L : Link S Claim) (p : Where)
    (share : LinkShare L p) (movesQ : IsMoves atS [.quiet L.runBehind] L.behindB)
    (pq : Piece C F S Claim WT) (hpq : pq.b = below L.behindB) (hand : HandsOn Rz k pq)
    (hfen : fenceFit 𝔇.N links pl = true) (hb : 𝔇.N.treesAt pl[k]? ≤ pq.base)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (hs : ∀ s s' : S, s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s))
    (htin : ∀ a t, onK k a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn (𝔇.N.group m) t = true) :
    ∀ b τ c, onK k b → pq.ior.red.out b τ = some c → onK (k + 1) c :=
  h12_mgR 𝔇 𝔇.N links pl z Rz k m p1 p2 hlf hp9 hp1 hp2 hl hpc ht hm L p share pq hpq hand
    (oraQ_of 𝔇 links pl z Rz k hfen (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp1).1) L p share pq
      hpq hb hd hs)
    (total_behind 𝔇 links pl z Rz k m L movesQ pq hpq htin)

/-- **THE HAND-ON OVER THE ONE EQUATION** (k: that piece's border). -/
theorem ahon3_of (hlf : linkFit links pl = true) (hli : listFit links pl = true)
    (hpE : pubFitE moreAll links pl = true) (hN : rowsAtFit 𝔇.N links.length = true)
    (hml : m < links.length) (p1 p2 : Place) (hp1 : pl[k]? = some p1) (hp2 : pl[k + 1]? = some p2)
    (hl : p1.link = some m) (hpc : p1.piece = hearN links m + 3)
    (ht : 𝔇.N.treesAt pl[k + 1]? = 𝔇.N.treesAt pl[k]?)
    (hm : 𝔇.N.msgsAt pl[k + 1]? = 𝔇.N.msgsAt pl[k]?) (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim WT) (hpe : pe.b = below b₃) (hand : HandsOn Rz k pe)
    (hg : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → 𝔇.N.groupAt m = x.L.check.group)
    (hfen : fenceFit 𝔇.N links pl = true) (hb : 𝔇.N.treesAt pl[k]? ≤ pe.base)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (hsE : ∀ s s' : S, SameBy tri s.st s'.st → s'.book = s.book → 𝔇.smp (z, s') = 𝔇.smp (z, s))
    (notIx : ∀ a, onK k a → OwnNotIndex a.1) :
    ∀ c τ x, onK k c → pe.ior.red.out c τ = some x → onK (k + 1) x :=
  hon3_mgR 𝔇 𝔇.N links pl z Rz k m p1 p2 hlf hli hpE hN hml hp1 hp2 hl hpc ht hm pw b₃ hb₃ pe hpe
    hand hg
    (eqAsks_at 𝔇 links pl z Rz k hfen (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp1).1) pw b₃ hb₃
      pe hpe hb hd hsE notIx)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.quiet_nil
#print axioms VerifiableInference.Desc.LinkJoin.smpNamed_tri
#print axioms VerifiableInference.Desc.LinkJoin.total_behind
#print axioms VerifiableInference.Desc.LinkJoin.oraQ_of
#print axioms VerifiableInference.Desc.LinkJoin.eqAsks_at
#print axioms VerifiableInference.Desc.LinkJoin.ah12_of
#print axioms VerifiableInference.Desc.LinkJoin.ahon3_of
