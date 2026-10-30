--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/ShareAtMg.lean: THE RUNS' SHARE OF A LINK (`LinkShare L p`,
Johnson/Desc/First/Link/Law/: the batching is a draw with one adding move; the rows are not 0;
every relation that putFork keeps rides over all the link's runs; "K8.equations" stands in the
order; the sizes ride) AT ALL 25 LINKS OF THE CLOSED CONSTANT, FROM THE HEAD: WITH NO PREMISE THAT
NAMES A PROMISE. Theorems: one call each.

Why. A reader of the reading room noted: the laid road to "a mark stays" at K9's batching TAKES the
sort's whole own fields (share_of_layersOwesC ..), though it SPENDS only the ties and the fields "a
yes of the lookup's run keeps ..": so if another of these fields (h4, k3: the laws under the
promise) could not be met, the mark's clause would fall with it. THE CURE HERE: the sort's own
fields are general in the letter Kx, and h4 and k3 stand UNDER the promise fun q => ‹the named Ok›
q ∧ Kx q. AT Kx := fun _ => False THE PROMISE IS NEVER MET, SO h4, k3 AND THE PREMISES k3pl, k3jn
OF THE ASSEMBLIES HOLD IDLY: and LinkShare names no promise. So it follows from the assemblies at
that idle letter.

What is said. `share_layers_at`, `share_att_at`, `share_head_at`: **LinkShare L p**, from h (the
head), the opening O, m < 25, the sort of m, the link, that it is a segment, drawB, kp.

WHAT IT SHOWS, PLAINLY: LinkShare L p HOLDS AT THE LINK, WHETHER OR NOT THE LAWS UNDER THE TRUE
PROMISE (h4, k3, k3 at "planes" and "join") CAN BE MET THERE. LinkShare names neither Kx nor a
promise: so a proof through one instance of "for all Kx" proves the very proposition that the road
had from the true Kx.

WHAT IT DOES NOT SHOW: which fields share_of_layersOwesC, share_of_attOwesC, share_of_headOwesC
spend. At the idle letter h4 and k3 hold idly: a proof that spent them would pass just as well. (By
reading linkShare_layers .. in SortShare.lean: the sort's Take, of which rel_ and run_ read the
ties; k3p, k3s, k3sL; drawB; rows. That is a reading, not this file's result.)

THE IDLE INSTANCE IS SPENT FOR LinkShare ALONE, AND NOWHERE FOR A LAW UNDER THE PROMISE.

Limits. THE IDLE LETTER IS A DEVICE OF PROOF: NOTHING IS SAID HERE OF ANY PROMISE. The head and the
opening are premises; beneath the assemblies stand the ties, hψ, drawB, rows and the seven fields
"a yes of the lookup's run keeps .." at the lookup's entries. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.LPFK9R.LayersOwesWhole
import Johnson.LPFK9R.LookAttAtMg
import Johnson.LPFK9R.LookHeadAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription claimsInBy)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **THE RUNS' SHARE AT A LAYERS' LINK OF THE CONSTANT.** -/
theorem share_layers_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .layers) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) : LinkShare L p := by
  obtain ⟨p4, X, _, _, H⟩ := layersOwesC_whole h O m hm hs L p hlk seg drawB kp
  exact share_of_layersOwesC (H (fun _ => False) 0 0 0 0 (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _
    _ _ => 0) X.tl X.tl
    (fun _ hq => hq.elim))

/-- **THE RUNS' SHARE AT AN ATTENTION LINK OF THE CONSTANT.** -/
theorem share_att_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .attention) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) : LinkShare L p := by
  obtain ⟨Xl, A, X, _, _, _, _, H⟩ := attOwesC_whole h O m hm hs L p hlk seg drawB kp
  exact share_of_attOwesC (H (fun _ => False) 0 0 0 0 (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _
    _ => 0) X.tl X.tl
    (fun _ hq => hq.elim) (by intro run _ q front e a c e₁ hf; exact hf.1.2.elim)
    (by intro run _ q front e a c e₁ hf; exact hf.1.2.elim))

/-- **THE RUNS' SHARE AT THE HEAD's LINK OF THE CONSTANT.** -/
theorem share_head_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .head) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) : LinkShare L p := by
  obtain ⟨iU3, X, _, _, H⟩ := headOwesC_whole h O m hm hs L p hlk seg drawB kp
  exact share_of_headOwesC (H (fun _ => False) 0 0 0 0 (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _
    _ => 0) X.tl X.tl
    (fun _ hq => hq.elim) (by intro run _ q front e a c e₁ hf; exact hf.1.2.elim))

end LPFK9

#print axioms LPFK9.share_layers_at
#print axioms LPFK9.share_att_at
#print axioms LPFK9.share_head_at
