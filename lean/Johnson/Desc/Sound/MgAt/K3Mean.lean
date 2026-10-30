-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Mean.lean: the kind "lookup" (K3): THE JOIN: `K3MeanR`
(Johnson/Desc/First/Look/K3MeansR.lean: all that the kind's fifty places ask of the meaning, second
form) AT THE COMPOSED MEANING `mgAll 𝔇 Mg`, AND SO K03_law THERE; with WHAT IS STILL
OWED AS ONE LEAN STRUCTURE.

Main names:
  `HeadRestR`: what is left at the output head's calls: the premises of `headMeanR_mgAll`
    (MgAt/K3HeadMean.lean) that are neither facts on the constant and the piece nor of every place.
  `K3RestR`: THE LEDGER: what K03_law still owes at the term, sort by sort: dig (`DigRestR`), att
    (`AttRestR`), lay (`LayRestR`): the lookups' authors' structures (K3DigitsRestR.lean,
    MgAt/K3CallsRestR.lean) · head (`HeadRestR`) · and seven sentences on 𝔇, Mg and Rch.
  `k3MeanR_mgAll`: `K3PlanR` · `K3Pieces` · `K3RestR` and hDl (Dl.up = 𝔇.sent) give `K3MeanR` at
    the term, at the named readers of OOD samples.
  `k03_law_mgAll`: so `KindTiedR 𝔇.N (mgAll 𝔇 Mg) … KindName.K3`, in the goals' scope.

lookAtt, lookLay (inside the fields att and lay): "the place that the public parameters lay IS the
one that the law reads". `attAt` and `layAt` return the laid place WITH ITS SHAPE REPLACED by the
shape that its calls fix; the lookups' authors' rules take both `lookAt X l false = some x` and
`attAt X l = some (x, …)` at one x: the two hold together just where the public parameters' own
shape is that shape: a test on the public parameters; not shown here.
(Where this and lean/THEOREM.md differ, the page holds.)

idx IS A LETTER OF EACH SEGMENT: idx l n: the place of the message of number n in segment l's own
list (Johnson/Goal/Meaning/ReadingsOne.lean: `entryTieB`). One idx for all 24 segments would not do:
a message that one segment owns and the next borrows stands at two places
in the two lists, so tie and one could not hold at both: such a ledger is, by reading (no theorem),
empty at the release's files.

Limits: `K3RestR` is a premise: shown at no 𝔇; NEITHER ITS FIELDS ALONE NOR TOGETHER TRIED FOR
EMPTINESS. Rch and E are letters. The full size's written lists alone. Nothing on soundness by
itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAt.K3HeadMean
import Johnson.Desc.Sound.MgAt.K3CallsRestR
import Johnson.Desc.Sound.MgAt.K3Digits
import Johnson.Desc.First.Look.K3LawOfR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning ModelPart shift)
open VerifiableInference.Desc (Wit)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- The full size's written list: an odd segment below 24 is attention's. -/
theorem links_att : ∀ l, l < 24 → l % 2 = 1 → linksFull[l]? = some ModelPart.attention := by
  decide +kernel

/-- An even one is the layers'. -/
theorem links_lay : ∀ l, l < 24 → l % 2 = 0 → linksFull[l]? = some ModelPart.layers := by
  decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

/-- **WHAT IS LEFT AT THE OUTPUT HEAD's CALLS.** -/
structure HeadRestR {Cl : Type} (claim : Aff → Cl) (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
    (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (arrs : Array (Nat × String)) (pl pl' : Desc.Place)
    (told : List (List Desc.Oracle)) : Prop where
  /-- a test on the public parameters -/
  hs : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape = some x.fs
  /-- on the numbers and the piece -/
  hbase : ∀ t ∈ 𝔇.N.sent 24 0, t.1 < q.base
  /-- on the list of rounds: three of `ListSits` -/
  hsome : ∀ i, ∃ y ∈ 𝔇.ms, Alike y
    ⟨callsSending x 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link false j.1), i⟩
  hsent : ∀ i : Fin (sigListCalls 𝔇.sent 𝔇.l3.rad x.link).length,
    𝔇.l3.seat x.link false i.1 ∈ 𝔇.N.sent 24 0
  hfits : Desc.Sound.SeatFits 𝔇.G 𝔇.sent.codes (sigListCalls 𝔇.sent 𝔇.l3.rad x.link)
    fun j => 𝔇.l3.seat x.link false j.1
  /-- where the piece accepts: the promise behind -/
  parts : ∀ B', SeatOf b' B' → ∀ z : P,
    BehindPartsR (Fr := Fr) x (Params.settingOf X.P.frame) 𝔇.N (mgAll 𝔇 Mg) linksFull PS z
      (k3K 24 false) 24 3 arrs pl pl' told
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch (k3K 24 false) ((z, u.1), u.2))
  /-- objects, model, smallBack -/
  left : ∀ B', SeatOf b' B' → ∀ z : P,
    letI := k3SizesAt X
    letI := k3PolicyAt X
    letI := 𝔇.rq z
    HeadLeftR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
      (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun u => Rch (k3K 24 false) ((z, u.1), u.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
  rides : RidesAtR 𝔇.N (mgAll 𝔇 Mg) Rch (k3K 24 false) q b'

variable (codes : Codes) (shape : Params.ReqShape)
  (pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl
    (Wit (CellsQ rows cols) Tok MsgT)))
  (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2)
  (tok : Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V)
  (nx : ℕ → Bool → Desc.Place) (told : List (List Desc.Oracle)) (arrs : Array (Nat × String))

/-- **THE LEDGER: WHAT K03_law STILL OWES AT THE TERM.** nx: the place behind each lookup
argument. -/
structure K3RestR : Prop where
  /-- on 𝔇 and Mg alone -/
  hM : Mg.more = {}
  hS : Stored.NoRec 𝔇.decT
  es : 𝔇.smp = smpNamed 𝔇.cs seats
  hD : 𝔇.digitsPart = digitsPartK3 X 𝔇.sent 𝔇.l3
  hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → 𝔇.decT c y' = 𝔇.decT c y
  hIn : InOrderReads Mg
  /-- what the kind spends of the facts along the fold -/
  fold : K3Fold Rch 𝔇.sent
  dig : ∀ l < 25, ∀ sub, linksFull[l]? = some sub → ∀ x tl, digAt X l = some (x, tl) →
    ∀ q, pieces[k3K l true]? = some q → ∀ b', k3Const X codes shape l true = some b' →
      DigRestR 𝔇.G X 𝔇.sent 𝔇.l3 𝔇.N (mgAll 𝔇 Mg) Rch K3Lot.ofForm 𝔇.smp 𝔇.ms (IM.k3Place l true)
        (nx l true) (k3K l true) l sub x tl (smpDigits seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b'
        told
  att : ∀ l < 25, ∀ x A tl, attAt X l = some (x, A, tl) →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      lookAt X l false = some x ∧
      AttRestR 𝔇 Mg Rch K3Lot.ofForm num (idx l) tls tok (IM.k3Place l false) (nx l false)
        (k3K l false) l x A tl (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  lay : ∀ l < 25, ∀ x tl, layAt X l = some x → tlAt X l = some tl →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      lookAt X l false = some x ∧
      LayRestR 𝔇 Mg Rch K3Lot.ofForm num (idx l) tls tok (IM.k3Place l false) (nx l false)
        (k3K l false) l x tl (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  head : ∀ x, Desc.Kinds.Head.Law.headAt X = some x →
    ∀ q, pieces[k3K 24 false]? = some q → ∀ b', k3Const X codes shape 24 false = some b' →
      HeadRestR 𝔇 Mg Rch K3Lot.ofForm seats s₀ x q b' arrs (IM.k3Place 24 false) (nx 24 false)
        told

variable {𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok nx told arrs}

/-- **`K3MeanR` AT THE TERM.** -/
theorem k3MeanR_mgAll {Dl : Desc.K3Asks.Sent} {floor : ℕ} (z₀ : P) (hDl : Dl.up = 𝔇.sent)
    (hP : letI := k3SizesAt X
      letI := k3PolicyAt X
      K3PlanR X Dl 𝔇.l3 floor)
    (hQ : K3Pieces X codes shape pieces)
    (R : K3RestR 𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok nx told arrs) :
    letI := k3SizesAt X
    letI := k3PolicyAt X
    K3MeanR 𝔇.G X codes shape 𝔇.sent 𝔇.l3 𝔇.N (mgAll 𝔇 Mg) Rch pieces
      (fun x => smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
      (fun x => smpDigits seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
      (Stored.smpWc (rows := rows) (cols := cols)) (fun z => Stored.strWc 𝔇.decT s₀ z)
      (k3AdrAt X) 𝔇.rq k3QAny (fun w => Flat.InRange w.cells) := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the digits
    intro l hl sub hsub x tl hx q hq b' hb
    obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b' hb
    obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
    obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
    exact digMeanR_mgAll 𝔇 Mg Rch K3Lot.ofForm (IM.k3Place l true) (nx l true) (k3K l true) l sub'
      x tl _ q b' told (K3Lot.readersAt X) codes shape hb (hQ.back l hl true q hq) hx rfl hsub hpcT
      hpc (K3Lot.k03_at_full l hl true) z₀ R.hD R.hd R.hIn
      (fun _ sb => smpNamed 𝔇.cs seats (z₀, { s₀ with st := sb.1, book := sb.2 }))
      (fun z s => by rw [R.es]; rfl) (R.dig l hl sub' hsub x tl hx q hq b' hb)
  · -- attention's calls
    intro l hl x A tl hx q hq b' hb
    obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l false b' hb
    obtain ⟨hlook, r⟩ := R.att l hl x A tl hx q hq b' hb
    have hsub := links_att l r.hlt r.odd
    obtain ⟨sub', hsub', hp2, -⟩ := K3Lot.k03_sub_full l hl
    obtain rfl : sub' = ModelPart.attention := Option.some.inj (hsub'.symm.trans hsub)
    obtain ⟨x', A', tl', hx', HA⟩ := hP.att l r.hlt r.odd
    obtain ⟨rfl, rfl, rfl⟩ : x' = x ∧ A' = A ∧ tl' = tl := by
      have e := Option.some.inj (hx'.symm.trans hx)
      exact ⟨congrArg Prod.fst e, congrArg (fun t => t.2.1) e, congrArg (fun t => t.2.2) e⟩
    rw [hDl] at HA
    exact attMeanR_of_rest (K3Lot.readersAt X) codes shape z₀ hb (hQ.planOk l hl false b' hb)
      (hQ.back l hl false q hq) rfl hpc hp2 hsub (K3Lot.k03_at_full l hl false) hlook hx HA r
  · -- the layers' calls
    intro l hl x tl hx htl q hq b' hb
    obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l false b' hb
    obtain ⟨hlook, r⟩ := R.lay l hl x tl hx htl q hq b' hb
    have hsub := links_lay l r.hlt r.even
    obtain ⟨sub', hsub', hp2, -⟩ := K3Lot.k03_sub_full l hl
    obtain rfl : sub' = ModelPart.layers := Option.some.inj (hsub'.symm.trans hsub)
    obtain ⟨x', tl', hx', -, HL, -⟩ := hP.lay l r.hlt r.even
    obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
    exact layMeanR_of_rest (K3Lot.readersAt X) codes shape z₀ s₀ hb (hQ.planOk l hl false b' hb)
      (hQ.back l hl false q hq) rfl hpc hp2 hsub (K3Lot.k03_at_full l hl false) hlook hx htl HL r
  · -- the head's calls
    intro x hx q hq b' hb
    obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape 24 false b' hb
    have r := R.head x hx q hq b' hb
    have e : placeAt X 24 false =
        some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) := by
      have e0 : placeAt X (headLink X) false =
          some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) :=
        letI : Desc.Kinds.Head.Request := ⟨fun _ => 0, 0, 0⟩
        placeAt_headAt hx
      rwa [hP.head24] at e0
    exact headMeanR_mgAll 𝔇 Mg K3Lot.ofForm (K3Lot.readersAt X) codes shape x seats Rch
      (IM.k3Place 24 false) b' q s₀ hb (hQ.planOk 24 (by decide) false b' hb) rfl hpc e
      (hQ.back 24 (by decide) false q hq) r.hs hx hP.head24 R.hM R.hS R.es r.hbase r.hsome r.hsent
      r.hfits R.fold r.parts r.left r.rides

end

section
open VerifiableInference.Desc (KindName)

/-- **K03_law AT THE COMPOSED MEANING, IN THE GOALS' SCOPE, FROM THE PUBLIC PARAMETERS' TESTS, THE
FACTS ON THE PIECES AND THE LEDGER.** hE: the table's extractor lays nothing at the kind's
places. -/
theorem k03_law_mgAll {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
    {Tok Xi : Type} {rows cols nR : ℕ} {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    {T : ThreeAt (ckP .two) D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    (hT : OfDesc _ T) (𝔇 : MgData Xi ProofFile.InstPub Tok rows cols nR Bs.G₀.W)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (Rch : ℕ → (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (E : ℕ → (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      Wit (CellsQ rows cols) Tok MsgT → Wit (CellsQ rows cols) Tok MsgT)
    (hE : ∀ l, l < 25 → ∀ d : Bool, ∀ a b w, E (k3K l d) a b w = w)
    {seats : List (ℕ × ℕ)} {s₀ : Desc.First.S} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ → ℕ}
    {tls : ℕ → HTailF2} {tok : Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V}
    {nx : ℕ → Bool → Desc.Place} {told : List (List Desc.Oracle)}
    {arrs : Array (Nat × String)}
    {Dl : Desc.K3Asks.Sent} {floor : ℕ} (z₀ : ProofFile.InstPub) (hDl : Dl.up = 𝔇.sent)
    (hP : letI := k3SizesAt Bs.G₀.W
      letI := k3PolicyAt Bs.G₀.W
      K3PlanR Bs.G₀.W Dl 𝔇.l3 floor)
    (hQ : K3Pieces Bs.G₀.W Z.first.codes Z.first.shape (T.p₁ :: T.l₁))
    (R : K3RestR 𝔇 Mg Rch Z.first.codes Z.first.shape (T.p₁ :: T.l₁) seats s₀ num idx tls tok nx
      told arrs) :
    KindTiedR 𝔇.N (mgAll 𝔇 Mg) linksFull PS Rch E (T.p₁ :: T.l₁) KindName.K3 := by
  letI := k3SizesAt Bs.G₀.W
  letI := k3PolicyAt Bs.G₀.W
  have M := k3MeanR_mgAll z₀ hDl hP hQ R
  rw [← hDl] at M
  exact k03_law_ofR hS hR O hT 𝔇.N (mgAll 𝔇 Mg) Rch E hE 𝔇.G Dl 𝔇.l3 hP hQ M

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.links_att
#print axioms VerifiableInference.OnPublicFiles.links_lay
#print axioms VerifiableInference.OnPublicFiles.k3MeanR_mgAll
#print axioms VerifiableInference.OnPublicFiles.k03_law_mgAll
