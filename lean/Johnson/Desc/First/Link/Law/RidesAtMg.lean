-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RidesAtMg.lean: «AN ACCEPTING TRANSCRIPT HANDS THE CONDITION ON», AT THE
TABLE's OWN PROMISE AT THE COMPOSED MEANING (`onT … (mgAll 𝔇 mgBase) …`), OVER A LINK's THREE QUIET
SUB-PROTOCOLS OF THE BATCHING KIND AND THE FRAME (our files call a sub-protocol a block): the link
law's premises h01 and h12, and the shutting's «hands». Theorems: RidesAt.lean's three with
`MgRides` paid by MgRidesAt.lean.

What is said.
  `LinkShare L pp`: the runs' share of a link, in one structure: the batching is a draw with the
    link's own gatherer behind it; its round counts a row; every run of the two orders stands in
    whatever relation rests under the known writings; the approximate range proof's equations stand
    in the order; every run passes «a ledger is open and has its sizes», with and without «as many
    sums on slots as slots». `quiet_batch`, `quiet_behind`, `quiet_shut`: `QuietAsks` at a piece's
    accepting transcript. `h01_mg`, `h12_mg`, `hands_mg`: **`onT … k a` and the piece's accepting
    transcript give `onT … (k + 1) b`, at the composed meaning**, from two Bools on the tables and
    the written list (`linkFit`, `pubFit9`), the place, the plan's two counts, `LinkShare`, and
    `OracleAsks` at each pair of states; h12_mg beside from «the one sum can be taken» behind.

Limits. PREMISES THAT STAY: `LinkShare` (LinkAtSort.lean and SizedRides.lean pay it at each sort
from the sort's Take and from the lookup's files' sentences on its runs: the ties of a link's
entries to these runs are owed); the plan's two counts (CountsFit.lean); `OracleAsks`: by nobody;
«the one sum can be taken»: by nobody. The one equation's piece (hon3) is not here. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.MgRidesAt
import Johnson.Desc.First.Link.Law.RidesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run.PQ (CK)

/-- **The runs' share of a link.** -/
structure LinkShare (L : Link S Claim) (pp : Where) : Prop where
  hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : pp.rows ≠ 0
  stand : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B
  eqIn : ∃ oE ∈ L.order, ∀ run, At L oE run → Under run k8Run.2
  sizedLS : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
    HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e →
      HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁
  sized : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
    HasFork Sized e → HasFork Sized e₁

theorem LinkShare.two {L : Link S Claim} {pp : Where} (h : LinkShare L pp) : TwoBlocks L pp := by
  obtain ⟨oE, hoE, hE⟩ := h.eqIn
  exact two_blocks L pp h.rows h.hb₁ h.stand oE hoE hE

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT

/-- QuietAsks over the batching's piece. -/
theorem quiet_batch (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (L : Link S Claim) (pp : Where) (h : LinkShare L pp) (pb : Piece C F S Claim WT)
    (hpb : pb.b = below L.batchB) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C pb.ds))
    (hout : pb.ior.red.out a τ = some b)
    (O : OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k pb.base a.1 b.1) :
    QuietAsks (C := C) 𝔇 Nm links pl z k m 1 a b := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact ⟨(h.two.1 _ _ _ _ _ j hstep).1,
    ⟨{ check := a.1.check }, {}, {}, (rest_blocks _ _ _ L pp h.hb₁ h.stand).1 _ _ _ _ _ j hstep⟩,
    ledger_batch L pp h.hb₁ h.sizedLS _ _ _ _ _ j hstep,
    ⟨pb.base, pb.ds, τ, out_strs hout, O⟩, fun e => absurd e (by decide)⟩

/-- QuietAsks over the piece of the frame's sub-protocol behind the batching. -/
theorem quiet_behind (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (L : Link S Claim) (pp : Where) (h : LinkShare L pp) (pq : Piece C F S Claim WT)
    (hpq : pq.b = below L.behindB) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C pq.ds))
    (hout : pq.ior.red.out a τ = some b)
    (O : OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k pq.base a.1 b.1)
    (ht : K9.totalIn (𝔇.pubD.N.group m) b.1 = true) :
    QuietAsks (C := C) 𝔇 Nm links pl z k m 2 a b := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact ⟨(h.two.2 _ _ _ _ _ j hstep).1,
    ⟨{ check := a.1.check }, {}, {}, (rest_blocks _ _ _ L pp h.hb₁ h.stand).2 _ _ _ _ _ j hstep⟩,
    ledger_behind L h.sized _ _ _ _ _ j hstep,
    ⟨pq.base, pq.ds, τ, out_strs hout, O⟩, fun _ => ht⟩

/-- QuietAsks over the shutting's piece. -/
theorem quiet_shut (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim WT) (hps : ps.b = below b₅) (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT C ps.ds)) (hout : ps.ior.red.out a τ = some b)
    (O : OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k ps.base a.1 b.1) :
    QuietAsks (C := C) 𝔇 Nm links pl z k m 5 a b := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hps hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact ⟨(rb_shutB pw piece b₅ hb₅ _ _ _ _ _ j hstep).1,
    ⟨{ check := a.1.check }, {}, {}, rest_shut _ _ _ pw piece b₅ hb₅ _ _ _ _ _ j hstep⟩,
    ledger_shut pw piece b₅ hb₅ _ _ _ _ _ j hstep,
    ⟨ps.base, ps.ds, τ, out_strs hout, O⟩, fun e => absurd e (by decide)⟩

/-- **h01 AT THE COMPOSED MEANING.** -/
theorem h01_mg (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (p p' : Place) (hfit : linkFit links pl = true) (hpf : pubFit9 true moreAll links pl = true)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 1)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (L : Link S Claim) (pp : Where) (h : LinkShare L pp) (pb : Piece C F S Claim WT)
    (hpb : pb.b = below L.batchB)
    (O : ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      pb.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k pb.base a.1 b.1) :
    ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      pb.ior.red.out a τ = some b →
      onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) (k + 1) b := by
  obtain ⟨⟨n1, n2⟩, hq, hw⟩ := fit_batch links pl hfit k m p p' hp hp' hl hpc
  exact h01_at Nm (mgAll 𝔇 mgBase) links pl z k p p' hp hp' hq ⟨n1, n2⟩ hw ht hm L pp h.two pb hpb
    fun a τ b ha hout => mgRides_at 𝔇 Nm links pl z k m 1 p hpf hp hl hpc (Or.inl rfl) a b
      (quiet_batch 𝔇 Nm links pl z k m L pp h pb hpb a b τ hout (O a τ b ha hout))

/-- **h12 AT THE COMPOSED MEANING.** -/
theorem h12_mg (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (p p' : Place) (hfit : linkFit links pl = true) (hpf : pubFit9 true moreAll links pl = true)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 2)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (L : Link S Claim) (pp : Where) (h : LinkShare L pp) (pq : Piece C F S Claim WT)
    (hpq : pq.b = below L.behindB)
    (O : ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      pq.ior.red.out a τ = some b → OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k pq.base a.1 b.1)
    (T : ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      pq.ior.red.out a τ = some b → K9.totalIn (𝔇.pubD.N.group m) b.1 = true) :
    ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      pq.ior.red.out a τ = some b →
      onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) (k + 1) b := by
  obtain ⟨⟨n1, n2⟩, hq, hw⟩ := fit_behind links pl hfit k m p p' hp hp' hl hpc
  exact h12_at Nm (mgAll 𝔇 mgBase) links pl z k p p' hp hp' hq ⟨n1, n2⟩ hw ht hm L pp h.two pq hpq
    fun a τ b ha hout => mgRides_at 𝔇 Nm links pl z k m 2 p hpf hp hl hpc (Or.inr (Or.inl rfl)) a b
      (quiet_behind 𝔇 Nm links pl z k m L pp h pq hpq a b τ hout (O a τ b ha hout)
        (T a τ b ha hout))

/-- **THE SHUTTING's «hands» AT THE COMPOSED MEANING.** -/
theorem hands_mg (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (p p' : Place) (hfit : linkFit links pl = true) (hpf : pubFit9 true moreAll links pl = true)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 5)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim WT) (hps : ps.b = below b₅)
    (O : ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      ps.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k ps.base a.1 b.1) :
    ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      ps.ior.red.out a τ = some b →
      onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) (k + 1) b := by
  obtain ⟨⟨n1, n2⟩, hq, hnw⟩ := fit_shut links pl hfit k m p p' hp hp' hl hpc
  exact hands_at Nm (mgAll 𝔇 mgBase) links pl z k p p' hp hp' hq ⟨n1, n2⟩ hnw ht hm pw piece b₅ hb₅
    ps hps fun a τ b ha hout =>
      mgRides_at 𝔇 Nm links pl z k m 5 p hpf hp hl hpc (Or.inr (Or.inr rfl)) a b
        (quiet_shut 𝔇 Nm links pl z k m pw piece b₅ hb₅ ps hps a b τ hout (O a τ b ha hout))

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.h01_mg
#print axioms VerifiableInference.Desc.LinkJoin.h12_mg
#print axioms VerifiableInference.Desc.LinkJoin.hands_mg
