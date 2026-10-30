-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/TiedAtEntry.lean:
KIND K5 AT THE RULE OF COMPOSITION: THE TIE THAT THE CHAIN OF PROMISES ASKS OF THE BLOCK AT
EACH NUMBER AT WHICH AN ENTRY BEARS THE KIND, FROM THE RETURN OF THE VALUE THAT verify() LAYS, WITH
ALL THAT IS STILL OWED AS PREMISES OF ONE THEOREM.

Why. What stands between the kind's laws and the rule of composition was kept on a map. A map can
leave a row out; a theorem's list of premises cannot. Here tied_of_alone
(Johnson/P5K3R/SitsAny.lean) is called at K5's entry, with K5's files' law at the table's letters
(K05_seatLaws_atMg, Johnson/Desc/First/Att/K05AtMg.lean) for its premise SeatLaws. Every fact on
public data, on the flat list, on the list of places and on the plan is paid inside, from proofDataAndDecisionOfPublicFiles's
return (LawAtLaid.lean and PlaceAtFlat.lean in Johnson/H2K5R/, and under Johnson/Desc/First/Att/:
K05NextPlace.lean, K05PlanOfPublic.lean, GuardPlanDigits.lean).

  `K05_tied_at`: **the tie at one number k at which the first chain's flat list has an entry E that
    bears K5, GENERAL IN THE TABLE's TWO LISTS**: links (the segments' sorts) and ps (the places)
    are letters, as they are in tied_of_alone and in K05_seatLaws_atMg; three small facts are asked
    of them: links has attention at 2 g + 1; ps has the kind's place at k and the segment's piece 4
    at k + 1. So the tie can be had at a written list (Johnson/H2K5R/KindTied.lean) as well as at
    the plan's own row.
  `K05_tied_of_open`: **from an opening at the second hash function, F.planOk and the door's yes:
    BY NUMBER: at every k at which the first chain's flat list has an entry E that bears K5: TiedBy
    … k … at the table's own words**, at links := the plan's row of links, ps := the driver's list
    of places at a flag "several", WHICH IS PINNED: the flat list's places are ps (the statement's
    clause in front of the numbers). The group g is
    a helper, pinned by E's own place ⟨1, some (2 g + 1), 3, K5⟩; a, x and xd are the group's plan
    and the places of the segment's two lookups, each pinned by its equation.
  `K05_tied_at_entry`: the same from proofDataAndDecisionOfPublicFiles's return (two lines, over laid_opens,
    Johnson/H2K5R/LawAtLaid.lean). A caller who spends more than one theorem of K5's files opens
    once and calls the forms "…_of_open".
NO PREMISE K5Plan AND NO LETTERS for the two lookups' parameters, the digits'
shape and three numbers: K5Plan is shown inside (k5Plan_of_public; digits_shape), and the
meaning K5AtMg is asked at the terms themselves: the lookups' parameters at the setting that the
public parameters (the plan derived from the public files) name, Forest.elems a.fs, a.ns. PAID
INSIDE: that the entry is the lot's block, alone; PlanIs; the profile; k5AtN's return; its test on
the plan; the guard's yes; the plan; the two places; K5Place; K5Plan; the two places of the list at
k and k + 1; the lot's one conjunct more (seatLaws_dress); that the piece's block's declared rounds
are the kind's. The open sets O and Q and the relation R' are the table's own terms.
WHAT IS LEFT, ALL OF IT, AS PREMISES: TWELVE: on the rows of pieces: OfDesc; the piece at k. On
the piece, in the form in which the law on the maker's pieces hands them out: nothing is put
behind its rounds; its error is the cap; its stretch is, round by round, the data of its own block's
declared rounds (RoundIs, Johnson/Desc/Sound/Stretch.lean). On the table's numbers: K5Book. On the
table: what the row asks is open; readsOpen; rowsApart; ridersB. The meaning: K5AtMg (nine fields).
The extractor lays nothing. It stands at the second hash function itself, since tied_of_alone is
typed there; all in K5's files beneath it stands at every o. EMPTY wherever proofDataAndDecisionOfPublicFiles refuses; where
no entry bears K5 it says nothing, and nothing is owed. Whether the premises can be met together is
shown nowhere.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.LawAtLaid
import Johnson.H2K5R.PlaceAtFlat
import Johnson.P5K3R.SitsAny
import Johnson.Desc.First.Att.K05AtMg
import Johnson.Desc.Sound.SeatLawsDress
import Johnson.Desc.Sound.Stretch
import Johnson.Desc.First.Att.K05NextPlace
import Johnson.Desc.First.Att.K05PlanOfPublic
import Johnson.Desc.First.Att.GuardPlanDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc (Claim RoundAsG Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers start flatPlaces flatPlacesOf)

open Classical in
/-- **THE TIE AT ONE NUMBER, GENERAL IN THE TABLE's TWO LISTS**: links and ps are letters; of them
three
small facts are asked: attention at 2 g + 1; the kind's place at k; the segment's piece 4 at k + 1.
-/
theorem K05_tied_at {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)} {c : Chain First.S Claim}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction pol lay KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : WholeD} (hs : ∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction pol lay KL F D, t.2 = true)
    {k : ℕ} {E : Block First.S Claim} (hfl : c.blocksInOrder[k]? = some E) (hK : E.place.kind = .K5) :
    ∃ (g : ℕ) (a : Attention.Plan) (x xd : VerifiableInference.Desc.First.Look.Place),
    Bs.G₀.W.p4 = true ∧ g < Bs.G₀.W.NGr ∧ E.place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
    Bs.G₀.W.A[g]? = some a ∧ lookAt Bs.G₀.W (2 * g + 1) false = some x ∧
    lookAt Bs.G₀.W (2 * g + 1) true = some xd ∧
    ∀ (links : List ModelPart) (ps : List Place) (_ : links[2 * g + 1]? = some .attention)
      (_ : ps[k]? = some ⟨1, some (2 * g + 1), 3, .K5⟩)
      (_ : ps[k + 1]? = some ⟨1, some (2 * g + 1), 4, .K1⟩)
      {D' : WholeD} {all : List LeftT} {X₁ X₂ W Cl' : Type}
      {T : ThreeAt (ckP .two) D' all
        (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        X₁ X₂ W}
      (_ : OfDesc _ T)
      {q : Sound.Piece (ckP .two) (Sound.frameAt D' all D'.key₁ T.ft₁) (ProofFile.InstPub × First.S)
        Claim W}
      (_ : (T.p₁ :: T.l₁)[k]? = some q)
      (_ : q.back = []) (_ : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
      (num : Fmt.TreeSource → ℕ)
      (_ : List.Forall₂ (fun d r => VerifiableInference.Desc.Sound.RoundIs num r d) q.ds
        q.b.rounds)
      (claim : Aff → Cl') (Ds : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
      (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
      (tj : OnBytes.K.Kc.Tape)
      (x0 : ProofFile.InstPub → First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str →
        TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
      (_ : First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → Ex.Str)
      (gOf : ProofFile.InstPub → First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → Forest.Heard)
      (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
      (I : PinItemP (Sound.frameAt D' all D'.key₁ T.ft₁) seatSO q.base W (attSg x Ds rad).Msg)
      (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (arr : Array (ℕ × String))
      (_ : K5Book N ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩)
      (_ : ∀ t ∈ (pubRowOf links ⟨1, some (2 * g + 1), 3, .K5⟩).asks,
        t ∈ (pubSets Mg.more links ps)[k]?.getD [])
      (_ : readsOpen links ps (start links) = true) (_ : rowsApart links ps = true)
      (_ : ridersB links ps k (2 * g + 1) = true)
      (_ : K5AtMg q.base claim Bs.G₀.W (2 * g + 1)
        ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) a x Ds rad Ex Wp α ns tj x0 gOf plJ I
        (fun π => relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k))
        N Mg links ⟨1, some (2 * g + 1), 3, .K5⟩ ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD [])
        (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) false x)
        (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) true xd) arr (Forest.elems a.fs)
        a.ns)
      (Ext : (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str →
        (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → W → W)
      (_ : ∀ u v w, Ext u v w = w),
      TiedBy N Mg links ps (fun u => u) k (q.withMap Ext) (onQ N Mg links ps (fun u => u) k)
        (onQ N Mg links ps (fun u => u) (k + 1))
        (relAt (meansQ N Mg fun u => u) (insQ links ps k))
        (relAt (meansQ N Mg fun u => u) (outsQ links ps k)) := by
  obtain ⟨-, hP, Hx⟩ := K05_facts_of_open O hpl hs
  obtain ⟨g, blk, a, x, h4, hg, hfl0, hla, hat, -, hok, hG, ea, hx, -⟩ :=
    Hx E (List.mem_of_getElem? hfl) hK
  obtain ⟨sv, hfp', -, hk0, -⟩ := K05_place_at O h4 hg
  have eP : E.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    rw [← hfp', List.getElem?_map, hfl0] at hk0
    exact Option.some.inj hk0
  obtain ⟨xd, hxd, -, -, hPn⟩ := k5Plan_of_public hP h4 ea hx (Params.settingOf Bs.G₀.W.P.frame)
  have Pn := hPn (digits_shape hP h4 ea hxd _)
  refine ⟨g, a, x, xd, h4, hg, eP, ea, hx, hxd, ?_⟩
  intro links ps hsub hk hk' D' all X₁ X₂ W Cl' T hT q hq hback herr num hrd claim Ds rad Ex Wp α ns
    tj x0 yOf gOf plJ I
    N Mg arr Bk hQ hr hap hB H Ext hExt
  have er : q.b.rounds = rounds (parO Bs.G₀.W (2 * g + 1) a
      ((H2K5.k5Before? Z ("A" ++ toString g)).getD [])) := by
    obtain ⟨a', ea', eb⟩ := k5AtN_is _ _ _ _ _ hat
    obtain rfl : a' = a := Option.some.inj (ea'.symm.trans ea)
    rw [OfDesc.pieceAt hT hq hfl]
    show E.rounds = _
    rw [(IM.alone_underR hla).1]
    show blk.rounds = _
    rw [eb]
    rfl
  have hds : List.Forall₂ RoundAsG q.ds (rounds (parO Bs.G₀.W (2 * g + 1) a
      ((H2K5.k5Before? Z ("A" ++ toString g)).getD []))) := by
    rw [← er]
    exact List.Forall₂.imp
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.1⟩) hrd
  haveI : Nonempty ProofFile.InstPub := ⟨⟨ByteArray.empty, default⟩⟩
  have HS := K05_seatLaws_atMg q hback herr claim hP h4 g (2 * g + 1) rfl _ blk hat hok hG ea hx Ds
    rad Ex Wp α ns hds tj x0 yOf gOf plJ I _ N Mg links _ _ _ _ _ _ _ arr _ _ _
    ⟨rfl, rfl, hsub, rfl, rfl⟩ Bk Pn hQ ps k hk hk' rfl rfl (fun _ => rfl) hr hap hB H
  exact K3Lot.tied_of_alone hT hfl hla (fun e => nomatch e) hq _ _ N Mg Ext hExt
    (seatLaws_dress _ _ _ q N Mg blk _ HS)

open Classical in
/-- **THE TIE, FROM AN OPENING**: at every number at which an entry bears the kind. -/
theorem K05_tied_of_open {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)} {c : Chain First.S Claim}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction pol lay KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : WholeD} (hs : ∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction pol lay KL F D, t.2 = true) :
    ∃ several, c.blocksInOrder.map (·.place) = flatPlaces true (ProofFile.subsOf Z) several ∧
      ∀ (k : ℕ) (E : Block First.S Claim), c.blocksInOrder[k]? = some E → E.place.kind = .K5 →
        ∃ (g : ℕ) (a : Attention.Plan) (x xd : VerifiableInference.Desc.First.Look.Place),
        E.place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
        Bs.G₀.W.A[g]? = some a ∧ lookAt Bs.G₀.W (2 * g + 1) false = some x ∧
        lookAt Bs.G₀.W (2 * g + 1) true = some xd ∧
        ∀ {D' : WholeD} {all : List LeftT} {X₁ X₂ W Cl' : Type}
          {T : ThreeAt (ckP .two) D' all
            (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
            X₁ X₂ W}
          (_ : OfDesc _ T)
          {q : Sound.Piece (ckP .two) (Sound.frameAt D' all D'.key₁ T.ft₁) (ProofFile.InstPub × First.S)
            Claim W}
          (_ : (T.p₁ :: T.l₁)[k]? = some q)
          (_ : q.back = []) (_ : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
          (num : Fmt.TreeSource → ℕ)
          (_ : List.Forall₂ (fun d r => VerifiableInference.Desc.Sound.RoundIs num r d) q.ds
            q.b.rounds)
          (claim : Aff → Cl') (Ds : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
          (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
          (tj : OnBytes.K.Kc.Tape)
          (x0 : ProofFile.InstPub → First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str →
            TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
          (_ : First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → Ex.Str)
          (gOf : ProofFile.InstPub → First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → Forest.Heard)
          (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
          (I : PinItemP (Sound.frameAt D' all D'.key₁ T.ft₁) seatSO q.base W (attSg x Ds rad).Msg)
          (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (arr : Array (ℕ × String))
          (_ : K5Book N ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩)
          (_ : ∀ t ∈ (pubRowOf (ProofFile.subsOf Z) ⟨1, some (2 * g + 1), 3, .K5⟩).asks,
            t ∈ (pubSets Mg.more (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several))[
                          k]?.getD [])
          (_ : readsOpen (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
            (start (ProofFile.subsOf Z)) = true)
          (_ : rowsApart (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) = true)
          (_ : ridersB (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
            k (2 * g + 1) = true)
          (_ : K5AtMg q.base claim Bs.G₀.W (2 * g + 1)
            ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) a x Ds rad Ex Wp α ns tj x0 gOf plJ I
            (fun π => relAt (meansQ N Mg fun s => (π, s))
              (outsQ (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
                k))
            N Mg (ProofFile.subsOf Z) ⟨1, some (2 * g + 1), 3, .K5⟩
            ((openSets (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
              (start (ProofFile.subsOf Z)))[k]?.getD [])
            ((pubSets Mg.more (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several))[
                          k]?.getD [])
            (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) false x)
            (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) true xd) arr (Forest.elems a.fs)
            a.ns)
          (Ext : (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str →
            (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → W → W)
          (_ : ∀ u v w, Ext u v w = w),
          TiedBy N Mg (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) (fun u => u)
            k (q.withMap Ext)
            (onQ N Mg (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) (fun u => u)
              k)
            (onQ N Mg (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) (fun u => u)
              (k + 1))
            (relAt (meansQ N Mg fun u => u)
              (insQ (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
                k))
            (relAt (meansQ N Mg fun u => u)
              (outsQ (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
                k)) := by
  obtain ⟨Hb, several, h1⟩ := chainBy_first O.chain
  have hfp := VerifiableInference.Desc.First.flat_places Hb _ several c h1
  have efp : flatPlaces true (ProofFile.subsOf Z) several = flatPlacesOf (ProofFile.subsOf Z) several := rfl
  refine ⟨several, hfp, fun k E hfl hK => ?_⟩
  obtain ⟨g, a, x, xd, h4, hg, eP, ea, hx, hxd, H⟩ := K05_tied_at O hpl hs hfl hK
  obtain ⟨-, -, hsub, -, -⟩ := K05_place_at O h4 hg
  have hk : (flatPlaces true (ProofFile.subsOf Z) several)[k]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    rw [efp, ← hfp, List.getElem?_map, hfl, ← eP]
    rfl
  exact ⟨g, a, x, xd, eP, ea, hx, hxd, H _ _ hsub hk (k5_next_place _ _ hk)⟩

open Classical in
/-- **THE TIE AT EVERY ENTRY THAT BEARS THE KIND.** -/
theorem K05_tied_at_entry {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    (h : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction pol lay KL = .ok (D, r)) :
    ∃ F Z Bs base₀ c A B several, ProofFile.onlineDescription OnBytes.secondHashFunction pol lay KL = .ok F ∧
      IM.Open OnBytes.secondHashFunction pol lay KL F Z Bs base₀ c A B ∧
      c.blocksInOrder.map (·.place) = flatPlaces true (ProofFile.subsOf Z) several ∧
      ∀ (k : ℕ) (E : Block First.S Claim), c.blocksInOrder[k]? = some E → E.place.kind = .K5 →
        ∃ (g : ℕ) (a : Attention.Plan) (x xd : VerifiableInference.Desc.First.Look.Place),
        E.place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
        Bs.G₀.W.A[g]? = some a ∧ lookAt Bs.G₀.W (2 * g + 1) false = some x ∧
        lookAt Bs.G₀.W (2 * g + 1) true = some xd ∧
        ∀ {D' : WholeD} {all : List LeftT} {X₁ X₂ W Cl' : Type}
          {T : ThreeAt (ckP .two) D' all
            (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
            X₁ X₂ W}
          (_ : OfDesc _ T)
          {q : Sound.Piece (ckP .two) (Sound.frameAt D' all D'.key₁ T.ft₁) (ProofFile.InstPub × First.S)
            Claim W}
          (_ : (T.p₁ :: T.l₁)[k]? = some q)
          (_ : q.back = []) (_ : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
          (num : Fmt.TreeSource → ℕ)
          (_ : List.Forall₂ (fun d r => VerifiableInference.Desc.Sound.RoundIs num r d) q.ds
            q.b.rounds)
          (claim : Aff → Cl') (Ds : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
          (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
          (tj : OnBytes.K.Kc.Tape)
          (x0 : ProofFile.InstPub → First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str →
            TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
          (_ : First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → Ex.Str)
          (gOf : ProofFile.InstPub → First.S × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → Forest.Heard)
          (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
          (I : PinItemP (Sound.frameAt D' all D'.key₁ T.ft₁) seatSO q.base W (attSg x Ds rad).Msg)
          (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (arr : Array (ℕ × String))
          (_ : K5Book N ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩)
          (_ : ∀ t ∈ (pubRowOf (ProofFile.subsOf Z) ⟨1, some (2 * g + 1), 3, .K5⟩).asks,
            t ∈ (pubSets Mg.more (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several))[
                          k]?.getD [])
          (_ : readsOpen (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
            (start (ProofFile.subsOf Z)) = true)
          (_ : rowsApart (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) = true)
          (_ : ridersB (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
            k (2 * g + 1) = true)
          (_ : K5AtMg q.base claim Bs.G₀.W (2 * g + 1)
            ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) a x Ds rad Ex Wp α ns tj x0 gOf plJ I
            (fun π => relAt (meansQ N Mg fun s => (π, s))
              (outsQ (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
                k))
            N Mg (ProofFile.subsOf Z) ⟨1, some (2 * g + 1), 3, .K5⟩
            ((openSets (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
              (start (ProofFile.subsOf Z)))[k]?.getD [])
            ((pubSets Mg.more (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several))[
                          k]?.getD [])
            (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) false x)
            (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) true xd) arr (Forest.elems a.fs)
            a.ns)
          (Ext : (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str →
            (ProofFile.InstPub × First.S) × (Sound.frameAt D' all D'.key₁ T.ft₁).E.Str → W → W)
          (_ : ∀ u v w, Ext u v w = w),
          TiedBy N Mg (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) (fun u => u)
            k (q.withMap Ext)
            (onQ N Mg (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) (fun u => u)
              k)
            (onQ N Mg (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several) (fun u => u)
              (k + 1))
            (relAt (meansQ N Mg fun u => u)
              (insQ (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
                k))
            (relAt (meansQ N Mg fun u => u)
              (outsQ (ProofFile.subsOf Z) (flatPlaces true (ProofFile.subsOf Z) several)
                k)) := by
  obtain ⟨F, Z, Bs, base₀, c, A, B, hF, hpl, -, -, hs, O⟩ := laid_opens h
  obtain ⟨several, hp, H⟩ := K05_tied_of_open O hpl hs
  exact ⟨F, Z, Bs, base₀, c, A, B, several, hF, O, hp, H⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_tied_at
#print axioms VerifiableInference.Desc.First.Att.P.K05_tied_of_open
#print axioms VerifiableInference.Desc.First.Att.P.K05_tied_at_entry
