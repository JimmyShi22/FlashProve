-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/LawAtEntry.lean: ROW K05_sits, AND KIND K5's LAW IN
ONE STATEMENT AT THE ENTRY OF onlineDescription's OWN FIRST CHAIN: at link 2 g + 1's third hearing block, at
every o (the second hash function as a letter), at every number of groups: no scope. OVER THE
LIBRARY's OWN TEXT: ProofFile.onlineDescription (Johnson/Desc/ProofFile/OnlineDescription.lean) and K5's files'
lot (Johnson/Desc/ProofFile/Lot/K5.lean).

OVER WHAT IT STANDS:
the seats (Johnson/IMR/: PureJoin, SeatForm, PureChain, LotKinds, LaidFirst, SeatOpen, Subs,
K5Seat, FlatIx) ·
K5's files' laws with the gathering's returns (Returns has the field u3) ·
onlineDescription's return is a premise.

NOTES. (1) "before" is (k5Before? Z
"A‹g›").getD [], and the lot's block is the kind's constant with one more conjunct in its test on
the plan, "before can be made" (IM.k5Dress: the lot's own text): so the tie LaidAlone stands between
the entry b and that dressed block. (2) The law's inner statement
is one definition, K5InnerLaw. (3) K05_law_one_dressed
is the law at every block that is { blk with
planOk := blk.planOk && ok' } so seated.

THE ROW's LETTER, CLAUSE BY CLAUSE ("in every written description that seats this kind: the entry of
the description's list of blocks at each place of the kind is the constant of which the kind's law
speaks, at the plan's numbers, under the seat's wrappers alone, or its yes gives that law's
premise"):
  "every written description that seats this kind": the proof file's, onlineDescription o.
  "at each place of the kind": K05_sits' two halves: for every g below the number of groups the
    entry at link 2 g + 1, hearing block 2; and no other entry of the first chain: every entry of
    the first chain's flat list that bears the kind K5 is one of these (k5_only). Of the shared and
    the second chain's lists nothing is said.
  "is the constant of which the law speaks": k5AtN, with the lot's one conjunct more in planOk.
  "at the plan's numbers": W := the seat's own public record (publicOfO o's return), the link 2 g +
    1, the group g, Z := pubPlain o's return.
  "under the seat's wrappers alone": IM.LaidAlone: four wrappers: the mark's guard, the spot's name,
    the driver's place, the guard on the reply's seat; nothing joined behind.
  "or its yes gives that law's premise": K05_law_one_dressed: the law holds at the entry b.

Main names:
  `built_att`, `att_only`: the ground's attention links are the numbers 2 g + 1, g below the number
    of groups, where the proof covers attention, and no others.
  `k5_alone`: at an opening's letters, at every o: the entry is the seated constant, dressed, alone.
  `chainBy_first`, `k5_only`: no other entry bears K5. `first_is`: the chain c of an opening is the
    description's first chain.
  `K05_sits`: **the row.**
  `K5InnerLaw`: the kind's law at a block, as one proposition. `K05_law_one_dressed`: it holds at
    every block that is the lot's block so seated, with that block's own planOk.
  `K05_law_at_descPure`: **at a return F of onlineDescription o with F.planOk: for each g the entry b, the
    constant b' and the tie between them, and, where the guard says yes, the place x and K5InnerLaw
    at b.** PlanIs (planIs_publicO) and b.planOk (Keeps.planOk_blocks) are paid inside.
The guard's yes is a premise here. It is paid by the value's own return in LawAtLaid.lean.
WHAT IS LEFT: K5InnerLaw's own premises: the data round by round; K5AtOn; K5Behind; D and rad free.
EMPTY AT: on := False · R' := False; wherever onlineDescription o refuses; below profile 4.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.IMR.K5Seat
import Johnson.Desc.First.Att.K05LawSeated
import Johnson.Desc.First.Att.GuardPublicCut
import Johnson.Desc.First.Att.K05Only
import Johnson.Desc.First.Att.K05Links
import Johnson.Desc.PlanPasses
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc (Claim RoundAsG Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching)

section Sits
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)} {c : Chain First.S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The ground's attention links**, at every number of groups. -/
theorem built_att {G₀ : ProofFile.Ground} (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (h4 : G₀.W.p4 = true) {g : ℕ}
    (hg : g < G₀.W.NGr) :
    ∃ Xl, G₀.built[2 * g + 1]? = some Xl ∧ Xl.kind = 1 ∧ Xl.g = g ∧
      Xl.name = "A" ++ toString g := by
  obtain ⟨-, Gs, As, H, l₀, ls, Bl, h₀, hB, hl, eB⟩ := IM.ground_public hZ hG
  rw [h4] at h₀ hB hl
  obtain ⟨g0, a0, -, p0, -⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨-, -, -, p1, -⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  have s0 : Gs[g]? = some Gs[g] := Array.getElem?_eq_getElem (by omega)
  have t0 : As[g]? = some As[g] := Array.getElem?_eq_getElem (by omega)
  obtain ⟨-, q0⟩ := p0 g _ _ s0 t0
  obtain ⟨-, q1⟩ := p1 g _ _ s0 t0
  obtain ⟨ar, e⟩ := Meaning.zipped_place hB q0 q1
  rw [eB]
  exact ⟨_, e, rfl, rfl, rfl⟩

/-- **K5 AT THE ATTENTION LINKS: THE SEATED CONSTANT, ALONE: AT EVERY o, AT EVERY NUMBER OF
GROUPS.** -/
theorem k5_alone (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true) {g : ℕ}
    (hg : g < Bs.G₀.W.NGr) :
    ∃ (Lk : Link First.S Claim) (b b' : Block First.S Claim),
      c.links[2 * g + 1]? = some Lk ∧ Lk.hear[2]? = some b ∧
      k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some b' ∧
      IM.LaidAlone ProofFile.sameReply b (IM.k5Dress Z ("A" ++ toString g) b') b.name
        ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  obtain ⟨X0, eX0, k0, g0, n0⟩ := built_att O.pub O.blank h4 hg
  have hsub : (ProofFile.subsOf Z)[2 * g + 1]? = some .attention := by
    rw [IM.subs_of_kind O.blank eX0, k0]
    rfl
  have hk : (kindsBeforeBatching .attention (2 * g + 1 == 0))[2]? = some KindName.K5 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain (2 * g + 1) .attention hsub 2 .K5
      hk (by decide) (by decide) (by decide)
  obtain rfl : L = H2K5.lotN Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ H2K5.k5OwnN Z Bs.G₀ := by
    rcases IM.blocks_mem hb' with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  obtain ⟨l, Xl, b₀, eX, -, hat, rfl⟩ := IM.k5OwnN_mem hb''
  have ep' : b₀.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := ep
  have el : l = 2 * g + 1 := by
    have e0 := (k5AtN_states hat).2.2
    have e : (some l : Option ℕ) = some (2 * g + 1) := congrArg Place.link (e0.symm.trans ep')
    exact Option.some.inj e
  subst el
  obtain rfl : X0 = Xl := Option.some.inj (eX0.symm.trans eX)
  rw [g0, n0] at hat
  rw [n0] at hla
  have hla' : IM.LaidAlone ProofFile.sameReply b (IM.k5Dress Z ("A" ++ toString g) b₀) b.name
      ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    rw [IM.alone_name hla]
    exact hla
  exact ⟨Lk, b, b₀, e1, e2, hat, hla'⟩

/-- The harness's first chain is the driver's, at the plan's row of links. By unfolding, as inside
IM.chain_hear. (The proximity test's files have the like a step lower: chainC_ok.)
-/
theorem chainBy_first {fr : List (ProofFile.FrameRole × Block First.S Claim)}
    {road : ProofFile.Gather First.S Claim} (hc : ProofFile.chainBy Z base fr road = .ok c) :
    ∃ (Hb : VerifiableInference.Desc.First.Blocks First.S Claim) (several : Bool),
      VerifiableInference.Desc.First.firstChain Hb (ProofFile.subsOf Z) several = some c := by
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        exact ⟨_, _, h1⟩

/-- **The plan's row of links has attention at the odd numbers 2 g + 1 alone.** -/
theorem att_only {G₀ : ProofFile.Ground} (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {l : ℕ}
    (hsub : (ProofFile.subsOf Z)[l]? = some .attention) :
    G₀.W.p4 = true ∧ ∃ g, g < G₀.W.NGr ∧ l = 2 * g + 1 := by
  have hB0 := IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB0
  obtain ⟨-, -, eW, -, -⟩ := IM.blank_ground hG
  rw [eW]
  unfold ProofFile.subsOf at hsub
  rw [List.getElem?_map] at hsub
  obtain ⟨bl, hb, ek⟩ := Option.map_eq_some_iff.1 hsub
  rw [Array.getElem?_toList] at hb
  have hk : bl.kind = 1 := by
    unfold ProofFile.subOf at ek
    split at ek
    · cases ek
    · split at ek
      · rename_i h1
        simpa using h1
      · cases ek
  obtain ⟨sz, hat⟩ := Meaning.built_at hB
  have hlt : l < l₀.size := by
    rw [← sz]
    exact (Array.getElem?_eq_some_iff.1 hb).1
  obtain ⟨ar, e1⟩ := hat l _ (Array.getElem?_eq_getElem hlt)
  have eb : bl = { l₀[l] with arrayOf := ar } := Option.some.inj (hb.symm.trans e1)
  have hk0 : l₀[l].kind = 1 := by
    rw [eb] at hk
    exact hk
  obtain ⟨Gs, As, Hh, h₀'⟩ : ∃ Gs As Hh,
      OnBytes.Model.Stages.listLinksH Z.p.X.NGr Z.p.X.p4 Gs As Hh = .ok l₀ := ⟨_, _, _, h₀⟩
  obtain ⟨h4, g, hg, el, -, -⟩ := links_kind1 h₀' (Array.getElem?_eq_getElem hlt) hk0
  exact ⟨h4, g, hg, el⟩

/-- **NO OTHER**: an entry of the first chain that bears the kind K5 is the third hearing block of
an attention link 2 g + 1. -/
theorem k5_only (O : IM.Open o pol lay KL F Z Bs base c A B) {E : Block First.S Claim}
    (hE : E ∈ c.blocksInOrder) (hK : E.place.kind = .K5) :
    Bs.G₀.W.p4 = true ∧ ∃ g, g < Bs.G₀.W.NGr ∧
      ∃ Lk : Link First.S Claim, c.links[2 * g + 1]? = some Lk ∧ Lk.hear[2]? = some E := by
  obtain ⟨Hb, several, h1⟩ := chainBy_first O.chain
  obtain ⟨l, Lk, hl, e1, e2⟩ := firstChain_k5_only Hb _ several c h1 E hE hK
  obtain ⟨h4, g, hg, rfl⟩ := att_only O.pub O.blank hl
  exact ⟨h4, g, hg, Lk, e1, e2⟩

/-- The chain c of an opening is the description's first chain: by unfolding. -/
theorem first_is (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (c : Chain First.S Claim) :
    (ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c).first = c := rfl

/-- **ROW K05_sits**: from onlineDescription's return, at every o. -/
theorem K05_sits (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z Bs base₀ c A B, IM.Open o pol lay KL F Z Bs base₀ c A B ∧
      ProofFile.pubPlain o pol lay KL = .ok Z ∧
      VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) = .ok Bs.G₀.W ∧
      (Bs.G₀.W.p4 = true → ∀ g < Bs.G₀.W.NGr,
        ∃ (Lk : Link First.S Claim) (b b' : Block First.S Claim),
          c.links[2 * g + 1]? = some Lk ∧ Lk.hear[2]? = some b ∧
          k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some b' ∧
          IM.LaidAlone ProofFile.sameReply b (IM.k5Dress Z ("A" ++ toString g) b') b.name
            ⟨1, some (2 * g + 1), 3, .K5⟩) ∧
      ∀ E ∈ c.blocksInOrder, E.place.kind = .K5 →
        Bs.G₀.W.p4 = true ∧ ∃ g, g < Bs.G₀.W.NGr ∧
          ∃ Lk : Link First.S Claim, c.links[2 * g + 1]? = some Lk ∧ Lk.hear[2]? = some E := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨Z, Bs, base, c, A, B, O, O.pub, (IM.ground_public O.pub O.blank).1,
    fun h4 g hg => k5_alone O h4 hg, fun E hE hK => k5_only O hE hK⟩

end Sits

open Classical in
/-- **The kind's law at the block b**, as one proposition: at every frame, type of worlds and
filling
of the composition's letters: from the data round by round against the kind's declared rounds, what
is asked at each statement in front with "on" (K5AtOn) and what is asked of the relation behind
(K5Behind), the piece at b, with error at most the cap at 128, is good: from "on" and the kind's own
relation in front (Todo) to the relation R' behind, with "laid behind", the promise that rides and
"no mark" promised behind. Wv: the public record; g: the group; before: the block's list of
commitments; a: the group's plan; x: the place of the segment's lookup. -/
def K5InnerLaw (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (b : Block First.S Claim)
    (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place) : Prop :=
  ∀ {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) (D : Sent) (rad : OracleShape → Nat)
    (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (_ : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (_ : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → W → Prop)
    (_ : K5AtOn x a.seam.tl D rad claim (parO Wv (2 * g + 1) a before) ns base x0 gOf pl on I Rd)
    (_ : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv (2 * g + 1) a before) ns base a.nW
      (plannedK a) (padOfO a.fs) tj gOf on I R'),
    (⟨b, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).GoodIn
      on (fun y => (LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on y ∧
        Rd.q (Rd.rq y.1) y.2) ∧ y.1.failed = none)
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w)) R'

/-- **THE LAW AT A BLOCK THAT IS THE LOT's BLOCK AS IT IS SEATED, ALONE**: the lot's block is blk
with
one more conjunct ok' in its test on the plan. -/
theorem K05_law_one_dressed {Wv : Verify.Public} (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ)
    (before : List (ℕ × ℕ)) (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (ok' : Bool) (b : Block First.S Claim)
    (n : String)
    (hla : IM.LaidAlone ProofFile.sameReply b { blk with planOk := blk.planOk && ok' } n
      ⟨1, some (2 * g + 1), 3, .K5⟩) (hokb : b.planOk = true)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) :
    K5InnerLaw Wv g before b a x := by
  unfold K5InnerLaw
  intro W Cl Fr claim D rad Ex Wp α ns base ds hds tj x0 yOf gOf pl on I Rd R' On Bh
  have hok : blk.planOk = true := by
    have e : (blk.planOk && ok') = true := (IM.alone_planOk hla).symm.trans hokb
    exact (Bool.and_eq_true_iff.1 e).1
  exact K05_law_one_under claim hP h4 g before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj
    x0 yOf gOf pl on I Rd R' On Bh b
    ((IM.alone_underR hla).trans ⟨rfl, fun _ _ _ _ e => e⟩) (fun s => s.failed = none)
    (fun s rs gs s' e => ((IM.yes_alone hla (fun e' => nomatch e') s s' rs gs).1 e).2.1)

/-- **THE LAW AT onlineDescription's OWN ENTRY**, at every o, at every number of groups. -/
theorem K05_law_at_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) (hpl : F.planOk = true) :
    ∃ Z Bs base₀ c A B, IM.Open o pol lay KL F Z Bs base₀ c A B ∧
      ProofFile.pubPlain o pol lay KL = .ok Z ∧
      VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) = .ok Bs.G₀.W ∧
      (Bs.G₀.W.p4 = true → ∀ g < Bs.G₀.W.NGr,
        ∃ (Lk : Link First.S Claim) (b b' : Block First.S Claim) (a : Attention.Plan),
        c.links[2 * g + 1]? = some Lk ∧ Lk.hear[2]? = some b ∧
        k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some b' ∧
        IM.LaidAlone ProofFile.sameReply b (IM.k5Dress Z ("A" ++ toString g) b') b.name
          ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
        Bs.G₀.W.A[g]? = some a ∧
        (k5GuardN Bs.G₀.W (2 * g + 1) g = true →
          ∃ x, lookAt Bs.G₀.W (2 * g + 1) false = some x ∧
            K5InnerLaw Bs.G₀.W g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) b a x)) := by
  obtain ⟨Z, Bs, base₀, c, A, B, O, hZ, hX, H, -⟩ := K05_sits hF
  refine ⟨Z, Bs, base₀, c, A, B, O, hZ, hX, fun h4 g hg => ?_⟩
  obtain ⟨Lk, b, b', e1, e2, hat, hla⟩ := H h4 g hg
  obtain ⟨a, ea, -⟩ := k5AtN_is _ _ _ _ _ hat
  have hP := planIs_publicO hX
  have hokb : b.planOk = true := by
    have hd := O.desc
    subst hd
    exact (VerifiableInference.Desc.Keeps.planOk_blocks _ hpl).1 b
      (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
  refine ⟨Lk, b, b', a, e1, e2, hat, hla, ea, fun hG => ?_⟩
  obtain ⟨x, -, hx, -, -⟩ := guard_binds hP ea hG
  exact ⟨x, hx, K05_law_one_dressed hP h4 g _ b' hat _ b b.name hla hokb hG ea hx⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.built_att
#print axioms VerifiableInference.Desc.First.Att.P.k5_alone
#print axioms VerifiableInference.Desc.First.Att.P.chainBy_first
#print axioms VerifiableInference.Desc.First.Att.P.att_only
#print axioms VerifiableInference.Desc.First.Att.P.k5_only
#print axioms VerifiableInference.Desc.First.Att.P.first_is
#print axioms VerifiableInference.Desc.First.Att.P.K05_sits
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_dressed
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_at_descPure
