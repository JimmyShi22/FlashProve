-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.Frame354
import Johnson.Loose.H2K12.K12LawR
import Johnson.Loose.H2K12.TileAtLast
import Johnson.Desc.Sound.DecodesAtPiece
import Johnson.Top.H0.Walk.Reach
/-
Johnson/Loose/H2K12/TieAt354.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN, sub-protocol
number 354 of the table's written list: THE FRAME, AT THE FILE's OWN PIECE. An assembly: what K12's
files have at that seat (the game: GameFirstCap, H2K12/TileAtLast.lean) is carried to the form in
which the kind's share of the chain of promises is asked (KindTiedR, Johnson/Desc/Sound/TiedR.lean),
UNDER FOUR NAMED PREMISES THAT ARE NOT PAID (T2At, T4aAt, T4bAt, T5At: H2K12/Frame354.lean).
  enterFinish_unmarked   the door's yes says that no test is marked as failed
  enters_of_sits   an accept of a piece that holds a sub-protocol which sits behind a door goes
                   through the door, and leaves the public part
  mark_of_sits     "a mark stays": no accept starts at a mark, so the clause is had because its two
                   premises clash; that is all that it says here
  dec_rides_354    "decodes rides": where the meaning's field is decodesOf decT and decT reads the
                   public part alone (decodes_at_piece_pub, Johnson/Desc/Sound/DecodesAtPiece.lean)
  tiedAtR_354_of   AT ANY PIECE q that holds such a sub-protocol and whose reduction leads, at its
                   own errors, to a Q that gives R354: the four named premises give TiedAtR at 354
  look_one         two look-ups in one list at one number return one thing
  pre_length_354   where the flat list's places are a list at which the test k12AllB passes, what
                   stands in front of a sub-protocol of the kind has 354 members
  first_inj        the first chain of a description that fileDescBy makes is the chain handed to it
  game_at_354      THE PIECE's TIE: in the goals' scope, at the letters Z N c at which the maker
                   returns K12's files' spelling descN of the IOP as written in Lean: the game
                   stands AT THE DESCRIPTION ITSELF (pulled along the identity, which is the
                   description: by unfolding), AT THE NUMBER 354, at any data D that the description
                   returns
  BackAt354 F D    the piece at 354 puts no round back; its base (tile_piece₁,
                   Johnson/Desc/K12/Coin/LawAtTileFirst.lean)
  Seat354 Z N D q  what is in hand of the piece in each of the four premises
  no354 N          the numbering of the book's places at which the game at this seat concludes
  k12_kind_of      LastTypedAt → KindTiedR … K12, at the first row of piecesAt with the cap as its
                   errors
WHAT IT IS NOT. A JOINING OVER LETTERS: IT PAYS NO LAW. The four premises hold all the content: an
accept keeps the table's promise; the game's conclusion gives one tuple of candidates; the tuple
gives the pins and the rows at the extractor's witness; every other open item rides back. Whether
they can be met together at the table's meaning and at the picked condition "reached" is shown
nowhere; where one of them is false the end says nothing. General in the meaning Mg, the numbers Nn,
the condition Rch, the extractors E. No example shows that game_at_354's premises hold together at
any files (evaluations alone say so). The Limits at the heads of H2K12/TileAtLast.lean and
H2K12/K12LawR.lean stand.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName Place FileDescription Strs Block Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Numbers start)

section
variable {Cl Cl' P W T : Type} {C : CK} {Fr : VerifiableInference.Desc.Sound.Frame}
  (q : Piece C Fr (P × VerifiableInference.Desc.First.S) Cl W)
  (B : Block VerifiableInference.Desc.First.S Cl)

/-- The door's yes says that no test is marked as failed. -/
theorem enterFinish_unmarked {s : VerifiableInference.Desc.First.S}
    {t : VerifiableInference.Desc.K12.T12}
    (h : VerifiableInference.Desc.K12.enterFinish s = .ok t) : s.failed = none := by
  unfold VerifiableInference.Desc.K12.enterFinish at h
  split at h
  · cases hf : s.failed with
    | none => rfl
    | some w =>
      exfalso
      cases hw : s.noneWaits <;>
        simp [VerifiableInference.Desc.need, hw, hf, bind, Except.bind] at h
  · cases h

/-- An accept of a piece that holds a sub-protocol which sits behind a door goes through the door,
and leaves the public part. -/
theorem enters_of_sits {K : Block T Cl'}
    {enter : VerifiableInference.Desc.First.S → Except String T}
    {leave : VerifiableInference.Desc.First.S → T → Except String VerifiableInference.Desc.First.S}
    (hb : q.b = held B) (hS : H2K.JointK.Sits B K enter leave)
    (a b : (P × VerifiableInference.Desc.First.S) × Fr.E.Str) (τ : Iop.Tr (uLT C q.ds))
    (h : q.ior.red.out a τ = some b) : b.1.1 = a.1.1 ∧ ∃ t, enter a.1.2 = .ok t := by
  obtain ⟨e, R, c, _, hs⟩ := Johnson.Desc.First.Walk.Tied.piece_step q B hb a b τ h
  obtain ⟨t, _, ht, _⟩ := hS.step _ _ _ _ _ _ hs
  exact ⟨e, t, ht⟩

/-- "A mark stays": no accept starts at a mark. -/
theorem mark_of_sits {K : Block VerifiableInference.Desc.K12.T12 Cl'}
    {leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S}
    (hb : q.b = held B)
    (hS : H2K.JointK.Sits B K VerifiableInference.Desc.K12.enterFinish leave) :
    ∀ a τ b, q.ior.red.out a τ = some b → a.1.2.failed ≠ none → b.1.2.failed ≠ none := by
  intro a τ b h hm
  obtain ⟨_, t, ht⟩ := enters_of_sits q B hb hS a b τ h
  exact absurd (enterFinish_unmarked ht) hm

/-- "Decodes rides", where decT reads the public part alone. -/
theorem dec_rides_354 {Cells : Type} {K : Block T Cl'}
    {enter : VerifiableInference.Desc.First.S → Except String T}
    {leave : VerifiableInference.Desc.First.S → T → Except String VerifiableInference.Desc.First.S}
    (Mg : VerifiableInference.Desc.First.Meaning P W)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (hb : q.b = held B) (hS : H2K.JointK.Sits B K enter leave)
    (hd : Mg.decodes = decodesOf decT)
    (hB : ∀ c (x x' : P × VerifiableInference.Desc.First.S), x'.1 = x.1 → decT c x' = decT c x) :
    ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2) := by
  intro a τ b h
  rw [hd]
  exact decodes_at_piece_pub decT hB (fun x => x) q a b τ h (enters_of_sits q B hb hS a b τ h).1

/-- **The tie at 354, at any piece that holds a sub-protocol which sits behind the door enterFinish
and whose reduction leads to a Q that gives R354: from the four named premises.** -/
theorem tiedAtR_354_of {Cells Xg : Type} (N : Numbers)
    (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place) (Rch : ℕ
          → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (e : (P × VerifiableInference.Desc.First.S) × Fr.E.Str →
      (P × VerifiableInference.Desc.First.S) × Fr.E.Str → W → W)
    {K : Block VerifiableInference.Desc.K12.T12 Cl'}
    {leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S}
    (hb : q.b = held B)
    (hS : H2K.JointK.Sits B K VerifiableInference.Desc.K12.enterFinish leave)
    (π : VerifiableInference.Desc.K12.P12) (no : VerifiableInference.Desc.K12.T12 → ℕ → ℕ)
    (rad : OnBytes.Slice.Sg → ℕ) (rdN : ℕ → ℕ)
    (Q : (P × VerifiableInference.Desc.First.S) × Fr.E.Str →
      (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (hQ : ∀ a b, Q a b → R354 Fr π no rad rdN a)
    (hL : q.ior.red.Leads (fun _ => True) Q q.err)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (hd : Mg.decodes = decodesOf decT)
    (hB : ∀ c (x x' : P × VerifiableInference.Desc.First.S), x'.1 = x.1 → decT c x' = decT c x)
    (cs : OnBytes.Codes) (G : FileDescription Xg)
    (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
    (mem : P × VerifiableInference.Desc.First.S → ℕ → Option Mem)
    (t2 : T2At N Mg links ps Rch 354 q)
    (t4a : T4aAt N Mg links ps Rch 354 q (R354 Fr π no rad rdN)
      (fun a => Tuple354 cs G smp (mem a.1) a.1 (strsOf Fr a.2)))
    (t4b : T4bAt N Mg links ps Rch 354 q e
      (fun a => Tuple354 cs G smp (mem a.1) a.1 (strsOf Fr a.2)))
    (t5 : T5At N Mg links ps Rch 354 q e) :
    TiedAtR N Mg links ps (fun a => a) Rch 354 (q.withMap e) :=
  (tiedByR_of_frame N Mg links ps Rch 354 q e _ _ (goodIn_of_leads q e _ Q hQ hL) t2 t4a t4b t5
    (mark_of_sits q B hb hS) (dec_rides_354 q B Mg decT hb hS hd hB)).tiedAtR

end

/-- Two look-ups in one list at one number return one thing. -/
theorem look_one {α : Type _} {L : List α} {n m : ℕ} {x y : α} (e : n = m) (h1 : L[n]? = some x)
    (h2 : L[m]? = some y) : x = y := by
  subst e
  exact Option.some.inj (h1.symm.trans h2)

/-- Where the flat list's places are a list at which the test k12AllB passes, what stands in front
of a sub-protocol of the kind has 354 members. -/
theorem pre_length_354 {S Cl : Type} {c : Chain S Cl} {pre l : List (Block S Cl)} {X : Block S Cl}
    {ps : List Place} (hc : c.blocksInOrder = pre ++ X :: l) (hX : X.place.kind = KindName.K12)
    (hpl : c.blocksInOrder.map (·.place) = ps) (hk : k12AllB ps = true) : pre.length = 354 := by
  have h1 : ps[pre.length]? = some X.place := by
    rw [← hpl, hc]
    simp
  exact (k12_places_of hk _ _ h1 hX).1

/-- The first chain of a description that fileDescBy makes is the chain that was handed to it. -/
theorem first_inj {o o' : ProofFile.SecondHashFunctionArgument} {mk mk' : ProofFile.LinksBy} {Z Z' : ProofFile.Pub}
    {A A' : ProofFile.SharedSeat} {B B' : ProofFile.SecondSeat}
    {g g' : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S}
    {s s' : ProofFile.InstPub → VerifiableInference.Desc.First.S}
    {c c' : Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (h : ProofFile.fileDescBy o mk Z A B g s c = ProofFile.fileDescBy o' mk' Z' A' B' g' s' c') : c = c' :=
  eq_of_heq (congr_arg_heq FileDescription.first h)

/-- K12's files' spelling of the proof file's IOP as written in Lean, at the plain road's links and
the parts guardedProximityTestParts. -/
abbrev FN (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl) : FileDescription ProofFile.Inst :=
  H2K.JointK.descN o ProofFile.pureRoad.links VerifiableInference.Desc.K12.guardedProximityTestParts Z N c

/-- At every filling of piecesAt's letters the piece number 354 of the first row puts no round back,
and its base is the number of trees in the first 48,237 rounds of the data's first chain. -/
def BackAt354 {Xi : Type} (F : FileDescription Xi) (D : WholeD) : Prop :=
  ∀ (W : Type) (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W), F.first.blocksInOrder = b₁ :: l₁ →
    ∀ p, ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[354]? = some p →
      p.back = [] ∧ p.base = 0 + VerifiableInference.Desc.Sound.nTrees (D.ds₁.take 48237)

/-- **THE PIECE's TIE: the game at the description itself, at the number 354.** -/
theorem game_at_354 {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {N : H2U.Places4}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {D : WholeD} {ps : List Place}
    (hS : VerifierAndGoals.InScope S = true) (hT : LastTypedAt o S.pol S.lay S.KL)
    (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (hN : H2U.placesOfMade Z.made = .ok N)
    (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (FN o Z N c)) (hp : (FN o Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol (FN o Z N c) = true)
    (hD : (FN o Z N c).data "proof file" = .ok D)
    (hk : k12AllB ps = true) (hpl : c.blocksInOrder.map (·.place) = ps) :
    ∃ pre J leave, pre.length = 354 ∧
      H2K.JointK.FirstOut ProofFile.sameReply (H2K.JointK.pL N) J leave ∧
      H2K.JointK.Sits (H2K.JointK.firstEntry ProofFile.sameReply J)
        (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2K.JointK.pL N) :
          H2K.JointK.Blk') VerifiableInference.Desc.K12.enterFinish leave ∧
      H2K.JointK.PublicAtLast Z N pre ∧
      H2K.JointK.GameFirstCap (FN o Z N c) D (H2K.JointK.pL N) H2K.Member.rLFull 48237
        VerifiableInference.Desc.K12.enterFinish leave 354
        (H2K.JointK.firstEntry ProofFile.sameReply J) ∧
      BackAt354 (FN o Z N c) D := by
  obtain ⟨Z', N', c', _, hZ', hN', e, _, pre, l, J, hb, _, hJ⟩ :=
    H2K.JointK.k12_sits o S.pol S.lay S.KL _ hF
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain rfl : N' = N := Except.ok.inj (hN'.symm.trans hN)
  obtain rfl : c' = c := (first_inj e).symm
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hLs := hT _ hZ
  obtain ⟨hW, _, _⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  obtain ⟨leave, hout, _, hg⟩ := H2K.JointK.game_at_descN_L o S.pol S.lay S.KL _ hZ _ _ _ hN hp A
    hLs hW ProofFile.sameReply pre l J hb hJ (fun x => x) D hD
  have hX : (H2K.JointK.firstEntry ProofFile.sameReply J).place.kind = KindName.K12 := by
    first
      | rfl
      | simp [H2K.JointK.firstEntry, Block.asBare, Block.guarded]
  have h354 : pre.length = 354 := pre_length_354 hb hX hpl hk
  obtain ⟨nm, eJ, rfl⟩ := hout
  have hPub := H2K.JointK.public_at_seat_L o S.pol S.lay S.KL _ hZ _ _ _ hN hp A hLs hW
    ProofFile.sameReply pre l J hb hJ
  have hSit := H2K.JointK.firstJ_sitsCore ProofFile.sameReply _ J hJ
  refine ⟨pre, J, _, h354, ⟨nm, eJ, rfl⟩, hSit, hPub, ?_, ?_⟩
  · first
      | exact h354 ▸ hg
      | (rw [← h354]; exact hg)
  obtain ⟨b', post, postR, r₀, rfl, hend⟩ := H2K.JointK.behind_L o S.pol S.lay S.KL _ hZ _ _ _ hN
    hp A hLs hW ProofFile.sameReply pre l J hb hJ
  obtain ⟨hl, C, _, ho, hfree, _, _⟩ := hPub
  intro W b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd q₁ p hp'
  obtain ⟨p', dB, dt, hp'', _, h0, hbase, _⟩ := VerifiableInference.Desc.K12.Coin.tile_piece₁
    _ "proof file" D hD b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd _
    H2K.Member.rLFull 128 pre (H2K.JointK.firstEntry ProofFile.sameReply J) b' post postR r₀ q₁
    (q₁.symm.trans hb) hend hSit.rounds hfree C.plan C.chain C.joh C.bat ho
  have ep : p' = p := look_one h354 hp'' hp'
  have hbase' := hbase.trans
    (congrArg (fun n => 0 + VerifiableInference.Desc.Sound.nTrees (D.ds₁.take n)) hl)
  subst ep
  exact ⟨h0, hbase'⟩

/-- What is in hand of the piece at 354 in each of the four premises. -/
def Seat354 {P W : Type} {C : CK} {Fr : VerifiableInference.Desc.Sound.Frame} (Z : ProofFile.Pub)
    (N : H2U.Places4) (D : WholeD)
    (q : Piece C Fr (P × VerifiableInference.Desc.First.S) ProofFile.Cl W) : Prop :=
  ∃ pre J leave, pre.length = 354 ∧ q.b = held (H2K.JointK.firstEntry ProofFile.sameReply J) ∧
    q.back = [] ∧ q.base = 0 + VerifiableInference.Desc.Sound.nTrees (D.ds₁.take 48237) ∧
    H2K.JointK.FirstOut ProofFile.sameReply (H2K.JointK.pL N) J leave ∧
    H2K.JointK.Sits (H2K.JointK.firstEntry ProofFile.sameReply J)
      (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2K.JointK.pL N) :
        H2K.JointK.Blk') VerifiableInference.Desc.K12.enterFinish leave ∧
    H2K.JointK.PublicAtLast Z N pre

/-- The first chain's own tree number 0 through the file is 0. -/
theorem numAt_own0 (t₁ t₂ : ℕ) : VerifiableInference.Desc.numAt t₁ t₂ 0 (.own 0) = 0 := rfl

/-- The numbering of the book's places at which the game at this seat concludes. -/
def no354 (N : H2U.Places4) (t : VerifiableInference.Desc.K12.T12) : ℕ → ℕ :=
  VerifiableInference.Desc.K12.Coin.nuOf (H2K.JointK.pL N)
    (VerifiableInference.Desc.K12.Coin.nlAt (H2K.JointK.pL N) 0) t

/-- **THE KIND's SHARE, FROM THE FOUR NAMED PREMISES**, at the first row of the pieces with the cap
as their errors. -/
theorem k12_kind_of {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {N : H2U.Places4}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {D : WholeD} {ps : List Place}
    (hS : VerifierAndGoals.InScope S = true)
    (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (hN : H2U.placesOfMade Z.made = .ok N)
    (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (FN o Z N c)) (hp : (FN o Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol (FN o Z N c) = true)
    (hD : (FN o Z N c).data "proof file" = .ok D)
    (hk : k12AllB ps = true) (hpl : c.blocksInOrder.map (·.place) = ps)
    {W Cells Xg : Type}
    (b₁ : Block (FN o Z N c).S₁ (FN o Z N c).Cl) (l₁ : List (Block (FN o Z N c).S₁ (FN o Z N c).Cl))
    (b₂ : Block (FN o Z N c).S₂ (FN o Z N c).Cl) (l₂ : List (Block (FN o Z N c).S₂ (FN o Z N c).Cl))
    (b₃ : Block (FN o Z N c).S₃ (FN o Z N c).Cl) (l₃ : List (Block (FN o Z N c).S₃ (FN o Z N c).Cl))
    (e₁ : (i : ℕ) → (ds : List RDT) →
      ((FN o Z N c).XiPub × (FN o Z N c).S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₂ : (i : ℕ) → (ds : List RDT) →
      (((FN o Z N c).XiPub × (FN o Z N c).S₁) × (FN o Z N c).S₂) ×
        (frameAt D (allOf D) D.key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₃ : (i : ℕ) → (ds : List RDT) →
      (((FN o Z N c).XiPub × (FN o Z N c).S₁ × (FN o Z N c).S₂) × (FN o Z N c).S₃) ×
        (frameAt D (allOf D) D.key₃ (FN o Z N c).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
    (d wEnd : W) (q₁ : (FN o Z N c).first.blocksInOrder = b₁ :: l₁)
    (Nn : Numbers) (Mg : VerifiableInference.Desc.First.Meaning ProofFile.InstPub W) (links : List ModelPart)
    (Rch : ℕ → (ProofFile.InstPub × VerifiableInference.Desc.First.S) ×
      (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (E : ℕ → (ProofFile.InstPub × VerifiableInference.Desc.First.S) ×
        (frameAt D (allOf D) D.key₁ 0).E.Str →
      (ProofFile.InstPub × VerifiableInference.Desc.First.S) × (frameAt D (allOf D) D.key₁ 0).E.Str →
      W → W)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × VerifiableInference.Desc.First.S →
      Option Cells)
    (hd : Mg.decodes = decodesOf decT)
    (hB : ∀ y (x x' : ProofFile.InstPub × VerifiableInference.Desc.First.S), x'.1 = x.1 →
      decT y x' = decT y x)
    (cs : OnBytes.Codes) (G : FileDescription Xg)
    (smp : ProofFile.InstPub × VerifiableInference.Desc.First.S → (s : Sending) →
      (i : Fin s.l.length) → Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
    (mem : ProofFile.InstPub × VerifiableInference.Desc.First.S → ℕ → Option Mem) (rdN : ℕ → ℕ)
    (owed : ∀ q : Piece (ckP .two) (frameAt D (allOf D) D.key₁ 0)
        (ProofFile.InstPub × VerifiableInference.Desc.First.S) ProofFile.Cl W,
      ((piecesAt (ckP .two) (FN o Z N c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).p₁ ::
        (piecesAt (ckP .two) (FN o Z N c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).l₁)[354]? = some q →
      Seat354 Z N D q →
      T2At Nn Mg links ps Rch 354 q ∧
      T4aAt Nn Mg links ps Rch 354 q
        (R354 (frameAt D (allOf D) D.key₁ 0) (H2K.JointK.pL N) (no354 N)
          (fun s => H2K.Member.rLFull s.st) rdN)
        (fun a => Tuple354 cs G smp (mem a.1) a.1 (strsOf (frameAt D (allOf D) D.key₁ 0) a.2)) ∧
      T4bAt Nn Mg links ps Rch 354 q (E 354)
        (fun a => Tuple354 cs G smp (mem a.1) a.1 (strsOf (frameAt D (allOf D) D.key₁ 0) a.2)) ∧
      T5At Nn Mg links ps Rch 354 q (E 354))
    (hT : LastTypedAt o S.pol S.lay S.KL) :
    KindTiedR Nn Mg links ps Rch E
      ((piecesAt (ckP .two) (FN o Z N c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).p₁ ::
        (piecesAt (ckP .two) (FN o Z N c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).l₁) KindName.K12 := by
  refine (kindTiedR_k12_iff Nn Mg Rch E _ links hk).2 fun q hq => ?_
  obtain ⟨pre, J, leave, h354, hout, hSits, hPub, hG, hBk⟩ :=
    game_at_354 hS hT hZ hN hF hp hpin hD hk hpl
  obtain ⟨p, hp', hb, _, hL⟩ := hG W b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d
    wEnd rdN q₁ (atCap_restCap e₁)
  obtain rfl : p = q := Option.some.inj (hp'.symm.trans hq)
  obtain ⟨h0, hbase⟩ := hBk W b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd q₁ _
    hq
  obtain ⟨t2, t4a, t4b, t5⟩ :=
    owed _ hq ⟨pre, J, leave, h354, hb, h0, hbase, hout, hSits, hPub⟩
  exact tiedAtR_354_of _ _ Nn Mg links ps Rch (E 354) hb hSits (H2K.JointK.pL N) (no354 N)
    (fun s => H2K.Member.rLFull s.st) rdN _
    (fun a b h => by
      obtain ⟨⟨⟨t, _, ht, _, hq'⟩, _⟩, _⟩ := h
      first
        | exact ⟨t, ht, hq'⟩
        | (rw [numAt_own0] at hq'; exact ⟨t, ht, hq'⟩)) hL decT hd hB cs G smp mem t2 t4a t4b t5

end H2K12

#print axioms H2K12.tiedAtR_354_of
#print axioms H2K12.pre_length_354
#print axioms H2K12.first_inj
#print axioms H2K12.game_at_354
#print axioms H2K12.k12_kind_of
