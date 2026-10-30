-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MadePublicPaid.lean: the kind "the code switch" (K2): THE
RECORD OF PREMISES `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean) AT THE FIRST THREAD's LETTERS AT
THE LIBRARY's HEAD, AT A SWITCH OF THE PLAN, BEHIND A STEP OF THE MEMBER, WITH ELEVEN OF ITS
TWENTY-ONE FIELDS PAID AND TEN HANDED ON. IT DOES NOT SAY THAT THE RECORD IS MET. One law, a join,
and one lemma on the form `SwitchArm`. No definition; nothing is evaluated here.

PAID, ALL PUBLIC: tables · groupRows · lengths · logC · logZ · first · count (`seven_at_yes`,
Honest/K2/Law/AtYesPublic.lean) · keptPos · restMain (`two_at_yes`, AtYesTarget.lean) · groupNo ·
inRange (`two_more_at_yes`, AtYesMore.lean). THESE THREE FILES COPY THE FIELDS' TEXTS; HERE LEAN
HOLDS THEM AGAINST THE RECORD ITSELF.

  `switchArm_unique`   at one place the form fixes the dress and the two steps
  `madeAsks_public_paid`   THE END. Its premises are those of the fourth limb of `SwitchPaid`
                    (Honest/K2/Law/ExchangeByKind.lean), as far as the eleven read them: the
                    thread's stand, the step, the two rounds, the step in front, `AtYes`, the step
                    behind. The kind's own yes, which groupNo and inRange want, is had from the
                    member's step by the way down (`k2_block_at_head`)

Limits. HANDED ON, IN THE RECORD's OWN TEXT (out of ExchangeAtMade.lean): fresh ·
carriedNo · positionNo · check · fits · seated (public; not paid) · honest · claim · stored ·
symbols (ON VALUES: PROVED OF NO RUN). A run's coins and the prover's state stand under the law's
binders, inside the thread's stand, of which the clause on how the state was made alone is read, and
inside the step, of which the member's own step alone is read. h: the library's head: A HYPOTHESIS.
All limits of the files named stand. NOT IN FRONT OF A LAW OVER COINS. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeAtMade
import Johnson.Desc.ProofFile.Honest.K2.Law.AtYesPublic
import Johnson.Desc.ProofFile.Honest.K2.Law.AtYesMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes KeptPos SameTables frameAt keptSamples targetRows
  decideWith)
open VerifiableInference.Desc.K2.Honest (Left OldFits SeatedAt sizesAt HonestMain ClaimTrue oldWords
  SymbolsAre carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)

/-- **At one place the form fixes the dress and the two steps.** -/
theorem switchArm_unique {Zp : ProofFile.Pub} {G : ProofFile.Ground} {p : SwitchPlace}
    {st st' : First.K2.At} {before before' : S → Except String S}
    {after after' : S → S → Except String S} (a : SwitchArm Zp G p st before after)
    (b : SwitchArm Zp G p st' before' after') :
    st = st' ∧ before = before' ∧ after = after' := by
  rcases a with ⟨rfl, -, -, a24, ai, rfl, fs, f, hfs, hff, -, rfl⟩ |
    ⟨rfl, -, ai, rfl, HP, hHP, rfl⟩ | ⟨rfl, -, ai, rfl, rfl⟩
  · rcases b with ⟨rfl, -, -, -, -, rfl, fs', f', hfs', hff', -, rfl⟩ | ⟨-, -, bi, -⟩ |
      ⟨-, -, bi, -⟩
    · obtain rfl : fs = fs' := Except.ok.inj (hfs.symm.trans hfs')
      obtain rfl : f = f' := Option.some.inj (hff.symm.trans hff')
      exact ⟨rfl, rfl, rfl⟩
    · omega
    · omega
  · rcases b with ⟨-, -, -, b24, bi, -⟩ | ⟨rfl, -, -, rfl, HP', hHP', rfl⟩ | ⟨-, -, bi, -⟩
    · omega
    · obtain rfl : HP = HP' := Option.some.inj (hHP.symm.trans hHP')
      exact ⟨rfl, rfl, rfl⟩
    · omega
  · rcases b with ⟨-, -, -, b24, bi, -⟩ | ⟨-, -, bi, -⟩ | ⟨rfl, -, -, rfl, rfl⟩
    · omega
    · omega
    · exact ⟨rfl, rfl, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {blk : Block TS ProofFile.Cl} {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **AT lettersHead, AT A SWITCH OF THE PLAN, BEHIND A STEP OF THE MEMBER: ELEVEN FIELDS OF
`MadeAsks` PAID, TEN HANDED ON** in the record's own text.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem madeAsks_public_paid
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (member : L.bs[P5J.At.ps.findIdx (· == p.place)]? = some blk)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) {nm : String} {st : First.K2.At}
    {before : TS → Except String TS} {after : TS → TS → Except String TS}
    (hA : SwitchArm Zp Bs.G₀ p st before after)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {Ev : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : ThrS L.thread Said (P5J.At.ps.findIdx (· == p.place)) k s m Ev)
    (hS : L.thread.Stepped blk k s m Ev ds y cols s')
    {V : Nat → Johnson.Prover.Send.Rows} {Wl : Left} {r₁ r₂ : Fmt.RoundView} {s₁ t : TS}
    {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (hr : (roundsOf y.1).map noDigest = [r₁, r₂]) (hb : before s = .ok s₁)
    (A : AtYes (IM.k2P Zp p.place nm st n) s₁ t r₁ r₂
      (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows G cd)
    (ha : after s₁ t = .ok s')
    (fresh : G.rows = #[])
    (carriedNo : ∀ W₀, frameAt x = some W₀ → L.N.rowsAt p.link .carried = (0, 1 + keptSamples x
      W₀))
    (positionNo : ∀ W₀, frameAt x = some W₀ → L.N.rowsAt p.link .position = (1 + keptSamples x W₀,
      r₂.drawn.poss.length * (1 + targetRows x.T + 2)))
    (check : switchTargetCheck S3 x.f.rows x.T = true)
    (fits : OldFits S3 x.f.rows)
    (seated : SeatedAt S3 x.f.rows x.T (z.ids.getD 0 noId) (z.ids.extract 1 (1 + x.T.kept.size)))
    (honest : HonestMain (sizesAt S3 x.f.rows x.T) Wl V)
    (claim : ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl)
    (stored : ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (S3.oracles.getD o
      default).sampleRows.toList, Says rdE S3 r (oldWords (sizesAt S3 x.f.rows x.T) x.f.rows Wl))
    (symbols : SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl (Positions.ofDraws (IM.k2P Zp
      p.place nm st n).logN r₂.drawn.poss) Y) :
    MadeAsks L.N p.link (switchPar p) (IM.k2P Zp p.place nm st n) s t s' V Wl r₂ x z S3 Y G := by
  obtain ⟨Pp', n', nm', st', before', after', hP', hn', hA', -, -, hdown⟩ :=
    k2_block_at_head h O hp (by rw [hL] at member; exact member)
  obtain rfl : Pp' = Pp := Option.some.inj (hP'.symm.trans hP)
  obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
  obtain ⟨rfl, rfl, rfl⟩ := switchArm_unique hA' hA
  have hy := ((VerifiableInference.Desc.Sound.step_ok_iff _ _ _ _ _ _ _).1 hS.2).2.2.2
  rw [hr] at hy
  obtain ⟨s₁', u, hb', hd, -⟩ := hdown s _ _ s' hy
  obtain rfl : s₁' = s₁ := Except.ok.inj (hb'.symm.trans hb)
  have hd' : decideWith sendByL8 (IM.k2P Zp p.place nm st' n') s₁' [r₁, r₂] _ = .ok u := hd
  obtain ⟨R, C, hf⟩ := fold_of_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL hT.1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := seven_at_yes h O hp hP hn hA hf hb nm A ha
  obtain ⟨b1, b2⟩ := two_at_yes h O hA hf hb nm A
  obtain ⟨c1, c2⟩ := two_more_at_yes h O hp hP hn nm hd' A
  subst hL
  exact { tables := a1, groupRows := a2, keptPos := b1, fresh := fresh, groupNo := c1
          carriedNo := carriedNo, positionNo := positionNo, check := check, restMain := b2
          fits := fits, seated := seated, lengths := a3, logC := a4, logZ := a5, inRange := c2
          first := a6, count := a7, honest := honest, claim := claim, stored := stored
          symbols := symbols }

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchArm_unique
#print axioms ProofFile.Honest.K2.Law.madeAsks_public_paid
