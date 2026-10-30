-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K8Seat.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K8's block (the smallness test) at its
place in every link of
onlineDescription's first chain, seated at the numbers of the public part's own plans.
OBJECT. THE SEATED CONSTANT: VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z G₀ Xl l) (Johnson/Desc/First/K8/Whole.lean · Johnson/Desc/ProofFile/Lot/K8.lean), Xl := G₀.built[l],
as it stands at F.first.links[l].hear[4] (the head's link: hear[5]).
USER. K8's laws at the seated block; the lookup's files; this folder's files on the tails.
LETTERS. As in Johnson/IMR/K6Seat.lean; Xl: HANDED OUT BY G₀.built[l]? = some Xl.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  ground_tails      in the goals' scope, at the blank letters G₀ of onlineDescription: the link at 2 g has tl · Fp · Tp · ns · NCL of G₀.W.G[g]; the link at 2 g + 1 has tl · Fp · Tp of G₀.W.A[g].seam and ns of
                    G₀.W.A[g]; the link at 24 has those of G₀.W.H.
  k8Whole_mem       a block of K8's lot is K8.whole (k8ParW Z G Xl l) at a link Xl of the list, at its number l.
  k8_alone          at an opening's letters, at every link l and index i = 4 | 5 at which kindsBeforeBatching has K8: the chain's block there IS seatedAs sameReply (K8.whole (k8ParW Z G₀ Xl l)) b.name ⟨1, some l, i + 1, K8⟩.
  k8_of_layers | k8_of_attention | k8_of_head    in scope: at 2 g · 2 g + 1 · 24, with the place's numbers tied: ks = ‹plan›.tl.mats.toList.map (·.k) · tau = ‹plan›.tl.tau (layers: and tl.NM = ks.length),
                    where ‹plan› is X.G[g] · X.A[g].seam · X.H.
  k8_alone_z        the three in one piece, from onlineDescription's value (one theorem, not three).
  k8_yes            b.decide s rs gs = ok t ↔ (K8.approximateRangeProofDrawKind K8.atS p.toPar).decide s rs gs = ok t ∧ t.failed = none ∧ sameReply s t = true (K8.whole has K8.approximateRangeProofDrawKind's decision, by its text).

WHO PAYS THE PREMISES: as in K6Seat.lean: that onlineDescription returns in scope is a premise.
What is not claimed. ms | asks | matsIn | readsIn | nU are not tied to the plans here. Nothing on what K8's laws ask beside these numbers. No soundness.
-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs
import Johnson.Goal.Meaning.Pub34Scope

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open OnBytes.L5.LinksOrder (zipped)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-! ## 1 The links' plans -/

/-- **In scope each link of the blank letters has its own plan's public fields.** -/
theorem ground_tails {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    (∀ g < 12, ∃ hp a l l', G₀.W.G[g]? = some hp ∧ G₀.W.A[g]? = some a ∧
        G₀.built[2 * g]? = some l ∧ l.tl = hp.tl ∧ l.Fp = hp.Fp ∧ l.Tp = hp.Tp ∧ l.ns = hp.ns ∧
        l.NCL = hp.NCL ∧
        G₀.built[2 * g + 1]? = some l' ∧ l'.tl = a.seam.tl ∧ l'.Fp = a.seam.Fp ∧
        l'.Tp = a.seam.Tp ∧ l'.ns = a.ns) ∧
      ∃ l, G₀.built[24]? = some l ∧ l.tl = G₀.W.H.tl ∧ l.Fp = G₀.W.H.Fp ∧ l.Tp = G₀.W.H.Tp ∧
        l.ns = G₀.W.H.ns ∧ l.NCL = G₀.W.H.NCL := by
  have hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← ProofFile.Law.blankBy_W hG]
    exact ground_publicK hZ hG
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts P.pol lay P.KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := plain_built hB
  obtain ⟨ls, hl, eW, eB, -⟩ := blank_ground hG
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  unfold ProofFile.Plain.linksPlain at h₀ hl
  rw [hq, hN] at h₀ hB hl
  obtain ⟨-, alt, l24, e24, I24⟩ := Meaning.links_alternate h₀ hB hl
  rw [eW, eB]
  refine ⟨fun g hg => ?_, l24, e24, I24.tl, I24.Fp, I24.Tp, I24.ns, I24.NCL⟩
  obtain ⟨s, a, l, l', es, ea, e, I, e', I'⟩ := alt g hg
  rw [Array.getElem?_map] at es ea
  obtain ⟨hp, ehp, rfl⟩ := Option.map_eq_some_iff.1 es
  obtain ⟨A, eA, rfl⟩ := Option.map_eq_some_iff.1 ea
  exact ⟨hp, A, l, l', ehp, eA, e, I.tl, I.Fp, I.Tp, I.ns, I.NCL, e', I'.tl, I'.Fp, I'.Tp, I'.ns⟩

/-! ## 2 K8's lot -/

/-- A block of K8's lot. -/
theorem k8Whole_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {b : Block S Cl} (h : b ∈ ProofFile.k8Whole Z G) :
    ∃ l Xl, G.built[l]? = some Xl ∧
      b = VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z G Xl l) := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  obtain ⟨Xl, l⟩ := x
  refine ⟨l, Xl, ?_, rfl⟩
  rw [← Array.getElem?_toList]
  simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hx)

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The chain's block at a place of kind K8 is K8's own, whole, alone, at the list's link of that number.** -/
theorem k8_alone (O : Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K8) (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk b Xl, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      (ProofFile.k8Par Z Bs.G₀ Xl l).piece = i + 1 ∧
      LaidAlone ProofFile.sameReply b (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl l))
        b.name { chain := 1, link := some l, piece := i + 1, kind := .K8 } := by
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain l sub hl i .K8 hk (by decide) (by decide) hi
  obtain rfl : L = ProofFile.P1K8.lot Z := lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ ProofFile.k8Whole Z Bs.G₀ := by
    rcases blocks_mem hb' with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  obtain ⟨l', Xl, eX, rfl⟩ := k8Whole_mem hb''
  have el : l' = l := by
    have e : (some l' : Option ℕ) = some l := congrArg Place.link ep
    exact Option.some.inj e
  subst el
  refine ⟨Lk, b, Xl, e1, e2, eX, congrArg Place.piece ep, ?_⟩
  rw [alone_name hla]
  exact hla

end

/-! ## 3 At the three sorts of link -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K8 AT THE LAYERS' LINKS.** -/
theorem k8_of_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (hp : Layer.HPlan2),
      c.links[2 * g]? = some Lk ∧ Lk.hear[4]? = some b ∧ Bs.G₀.built[2 * g]? = some Xl ∧
      LaidAlone ProofFile.sameReply b
        (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl (2 * g))) b.name
        { chain := 1, link := some (2 * g), piece := 5, kind := .K8 } ∧
      Bs.G₀.W.G[g]? = some hp ∧ (ProofFile.k8Par Z Bs.G₀ Xl (2 * g)).piece = 5 ∧
      (ProofFile.k8Par Z Bs.G₀ Xl (2 * g)).ks = hp.tl.mats.toList.map (·.k) ∧
      (ProofFile.k8Par Z Bs.G₀ Xl (2 * g)).tau = hp.tl.tau ∧
      hp.tl.NM = (ProofFile.k8Par Z Bs.G₀ Xl (2 * g)).ks.length := by
  intro g hg
  have hZ := O.pub
  have hG := O.blank
  have hX := O.public
  obtain ⟨tails, -⟩ := ground_tails hS hR hZ hG
  obtain ⟨hp, a, l, l', ehp, -, el, etl, -⟩ := tails g hg
  have hk : (kindsBeforeBatching .layers (2 * g == 0))[4]? = some KindName.K8 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, Xl, e1, e2, eX, epc, hla⟩ :=
    k8_alone O (2 * g) .layers (subs_at hS hR hZ hG hg) 4 hk (by decide)
  obtain rfl : l = Xl := Option.some.inj (el.symm.trans eX)
  have eks : (ProofFile.k8Par Z Bs.G₀ l (2 * g)).ks = hp.tl.mats.toList.map (·.k) := by
    show l.tl.mats.toList.map (·.k) = _
    rw [etl]
  refine ⟨Lk, b, l, hp, e1, e2, eX, hla, ehp, epc, eks, ?_, ?_⟩
  · show l.tl.tau = _
    rw [etl]
  · rw [eks, List.length_map, Array.length_toList]
    exact (Meaning.P34.tails_of_public hX ehp).2

/-- **K8 AT THE ATTENTION LINKS.** -/
theorem k8_of_attention (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (a : Attention.Plan),
      c.links[2 * g + 1]? = some Lk ∧ Lk.hear[4]? = some b ∧ Bs.G₀.built[2 * g + 1]? = some Xl ∧
      LaidAlone ProofFile.sameReply b
        (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl (2 * g + 1))) b.name
        { chain := 1, link := some (2 * g + 1), piece := 5, kind := .K8 } ∧
      Bs.G₀.W.A[g]? = some a ∧ (ProofFile.k8Par Z Bs.G₀ Xl (2 * g + 1)).piece = 5 ∧
      (ProofFile.k8Par Z Bs.G₀ Xl (2 * g + 1)).ks = a.seam.tl.mats.toList.map (·.k) ∧
      (ProofFile.k8Par Z Bs.G₀ Xl (2 * g + 1)).tau = a.seam.tl.tau := by
  intro g hg
  have hZ := O.pub
  have hG := O.blank
  obtain ⟨tails, -⟩ := ground_tails hS hR hZ hG
  obtain ⟨hp, a, l, l', -, ea, -, -, -, -, -, -, el', etl, -⟩ := tails g hg
  have hk : (kindsBeforeBatching .attention (2 * g + 1 == 0))[4]? = some KindName.K8 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, Xl, e1, e2, eX, epc, hla⟩ :=
    k8_alone O (2 * g + 1) .attention (subs_att hS hR hZ hG hg) 4 hk (by decide)
  obtain rfl : l' = Xl := Option.some.inj (el'.symm.trans eX)
  refine ⟨Lk, b, l', a, e1, e2, eX, hla, ea, epc, ?_, ?_⟩
  · show l'.tl.mats.toList.map (·.k) = _
    rw [etl]
  · show l'.tl.tau = _
    rw [etl]

/-- **K8 AT THE HEAD's LINK.** -/
theorem k8_of_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH),
      c.links[24]? = some Lk ∧ Lk.hear[5]? = some b ∧ Bs.G₀.built[24]? = some Xl ∧
      LaidAlone ProofFile.sameReply b
        (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl 24)) b.name
        { chain := 1, link := some 24, piece := 6, kind := .K8 } ∧
      (ProofFile.k8Par Z Bs.G₀ Xl 24).piece = 6 ∧
      (ProofFile.k8Par Z Bs.G₀ Xl 24).ks = Bs.G₀.W.H.tl.mats.toList.map (·.k) ∧
      (ProofFile.k8Par Z Bs.G₀ Xl 24).tau = Bs.G₀.W.H.tl.tau := by
  have hZ := O.pub
  have hG := O.blank
  obtain ⟨-, l, el, etl, -⟩ := ground_tails hS hR hZ hG
  have hk : (kindsBeforeBatching .head (24 == 0))[5]? = some KindName.K8 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, Xl, e1, e2, eX, epc, hla⟩ :=
    k8_alone O 24 .head (subs_head hS hR hZ hG) 5 hk (by decide)
  obtain rfl : l = Xl := Option.some.inj (el.symm.trans eX)
  refine ⟨Lk, b, l, e1, e2, eX, hla, epc, ?_, ?_⟩
  · show l.tl.mats.toList.map (·.k) = _
    rw [etl]
  · show l.tl.tau = _
    rw [etl]

end

/-- **The three in one piece, from onlineDescription's value.** -/
theorem k8_alone_z {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      ProofFile.onlineSharedChain Z = some A ∧ ProofFile.onlineLastChain Z = some B ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      (∀ g < 12, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (hp : Layer.HPlan2),
        c.links[2 * g]? = some Lk ∧ Lk.hear[4]? = some b ∧ G₀.built[2 * g]? = some Xl ∧
        LaidAlone ProofFile.sameReply b
          (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z G₀ Xl (2 * g))) b.name
          { chain := 1, link := some (2 * g), piece := 5, kind := .K8 } ∧
        X.G[g]? = some hp ∧ (ProofFile.k8Par Z G₀ Xl (2 * g)).piece = 5 ∧
        (ProofFile.k8Par Z G₀ Xl (2 * g)).ks = hp.tl.mats.toList.map (·.k) ∧
        (ProofFile.k8Par Z G₀ Xl (2 * g)).tau = hp.tl.tau ∧
        hp.tl.NM = (ProofFile.k8Par Z G₀ Xl (2 * g)).ks.length) ∧
      (∀ g < 12, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (a : Attention.Plan),
        c.links[2 * g + 1]? = some Lk ∧ Lk.hear[4]? = some b ∧ G₀.built[2 * g + 1]? = some Xl ∧
        LaidAlone ProofFile.sameReply b
          (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z G₀ Xl (2 * g + 1))) b.name
          { chain := 1, link := some (2 * g + 1), piece := 5, kind := .K8 } ∧
        X.A[g]? = some a ∧ (ProofFile.k8Par Z G₀ Xl (2 * g + 1)).piece = 5 ∧
        (ProofFile.k8Par Z G₀ Xl (2 * g + 1)).ks = a.seam.tl.mats.toList.map (·.k) ∧
        (ProofFile.k8Par Z G₀ Xl (2 * g + 1)).tau = a.seam.tl.tau) ∧
      ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH),
        c.links[24]? = some Lk ∧ Lk.hear[5]? = some b ∧ G₀.built[24]? = some Xl ∧
        LaidAlone ProofFile.sameReply b
          (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z G₀ Xl 24)) b.name
          { chain := 1, link := some 24, piece := 6, kind := .K8 } ∧
        (ProofFile.k8Par Z G₀ Xl 24).piece = 6 ∧
        (ProofFile.k8Par Z G₀ Xl 24).ks = X.H.tl.mats.toList.map (·.k) ∧
        (ProofFile.k8Par Z G₀ Xl 24).tau = X.H.tl.tau := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open hF
  exact ⟨Bs.G₀.W, Z, Bs.G₀, c, A, B, O.pub, O.public, O.blank, rfl, O.shared, O.second, O.desc,
    k8_of_layers hS hR O, k8_of_attention hS hR O, k8_of_head hS hR O⟩

/-- **The seated block's yes is the draw's block's yes at the carried record**, with no mark behind it and the reply as it was. -/
theorem k8_yes {b : Block S Cl} {p : VerifiableInference.Desc.First.K8.ParW} {name : String}
    {l i : ℕ}
    (h : LaidAlone ProofFile.sameReply b (VerifiableInference.Desc.First.K8.whole p) name
      { chain := 1, link := some l, piece := i, kind := .K8 }) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := Cl) VerifiableInference.Desc.First.K8.atS
        p.toPar).decide s rs gs = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true :=
  yes_alone h (fun e => nomatch e) s t rs gs

end IM

#print axioms IM.ground_tails
#print axioms IM.k8_alone
#print axioms IM.k8_of_layers
#print axioms IM.k8_of_attention
#print axioms IM.k8_of_head
#print axioms IM.k8_alone_z
#print axioms IM.k8_yes
