-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/HsemAt.lean: THE RECORDS' ROAD's END, AT THE TWO SIZES: the library's typed values
of the setting "record with work".
  fr_yes_desc | sr_yes_desc                 hsem of fr_link_joh | sr_link_joh AT dec := (descOf P
  plan ok).run (first, further): the conclusion of the library's fr_yes | sr_yes TO THE LETTER; hdec
  is gone
  fr_link_sound_desc | sr_link_sound_desc   UNDER Cb.BCHKS46At (a hypothesis: the theorem on codes):
  the library's written link at that decision is round-by-round sound for Sz.LangE2T at the pair of
  records r,
                                            at the library's own list of counts: fr_link_sound |
                                            sr_link_sound with hdec gone
  batOk                                     the general theorem's premise BatOk, PAID by bat_ok,
  Johnson/Desc/K12/Law/BatOk.lean (imported)
  decDescFull | decDescSmall                the decision at an instance: the description's run at
  the two keys written of it (keysOfX)
  H_full | H_small                          THE PREMISE H OF ANOTHER FILE's soundAt_full_of_joh |
  soundAt_small_of_joh (Johnson/Flat/Dec/SoundAtOfWritten.lean:70-77 | :115-122), TO THE LETTER, at
  decE := these: so
                                            that file's theorem gives its frame's named premise
                                            SoundAt … decE 2^-128 … (that file is not imported here)
PREMISES LEFT, ALL NAMED: Cb.BCHKS46At · P.set.samples = 1 · P.S | P.codes = recordRead's |
smallRecordRead's [evaluated true at another build's public files] · PubAt P frC | srC ·
OpensAt P frC | srC [both public; A MEMBER IS SHOWN, by the kernel, at the typed parameters frP |
srP: Johnson/Desc/K15/PubAtTyped.lean]. In H_full | H_small KeyHasR is paid (keyHasR_keyOf, as the
library pays it).
All that the heads of OnBytes/Slice/FullRecYes.lean, FullRecLink.lean and LinkChainJoh.lean do not
claim is not claimed here either: an interactive protocol; three ways out of the language; nothing
on hashes, bytes or the reader.

-/
import Johnson.Desc.K15.HsemProof
import Johnson.Desc.K12.Law.BatOk
import OnBytes.Slice.FullRecYes
import OnBytes.Slice.SmallRecYes
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open OnBytes.Params (recordRead smallRecordRead)
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- **BatOk is paid**: it is another file's theorem bat_ok (Johnson/Desc/K12/Law/BatOk.lean: in a
file of its own), to the letter. -/
theorem batOk : BatOk := fun S S' g e r row L h => H2K.ClaimSays.bat_ok S S' g e r row L h

/-! ## The full size -/

/-- **hsem of fr_link_joh at the description's own decision**: the conclusion of the library's
fr_yes to the letter; its premise hdec is gone. -/
theorem fr_yes_desc (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (first further : TableKey)
    (xs : List PQ.XO) (r : (frS.lkR frZ).X0) (hs : P.set.samples = 1) (hS : P.S = recordRead.link)
    (hC : P.codes = recordRead.codes) (hpub : PubAt P frC recordRead.codes) (hopen : OpensAt P frC)
    (hK0 : first.fits recordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1)
    (hK1 : further.fits recordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2)
    (y : (frS.lkR frZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : frC.Bl)
    (hacc : (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        (fun V => (descOf P plan ok).run (first, further) V)).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, frC.trL b) = true) :
    frC.Acc (sumStmR frN 97
        (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
            c5).1).1
        (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
            c5).1).2
        (drawnE (frRd 5) cA))
      (frW m2.1) (frF m2.1) (frW m2.1) b := by
  obtain ⟨set, codes, S, stages⟩ := P
  simp only at hS hC
  subst hS
  subst hC
  obtain ⟨_, hmems, hE, hm0, hst, hf1, hk, hR, h3, hz, hfm, hfz⟩ := fr_groupFacts
  exact yes_in_field_desc frS 97 29 1 _ plan ok first further recordRead.given.rounds (frRd 0)
      (frRd 1) (frRd 2)
    (frRd 3) (frRd 4) (frRd 5) frC xs batOk hs hpub hopen fr_h0 fr_headTrees fr_trees fr_len
    (rowShape recordRead.link) (maskShape recordRead.link) _ hmems hE hm0 _ hst hf1 hk hR h3 hz hfm
        hfz
    (by decide +kernel) fr_pads r hK0 hK1 fr_linkSizesR fr_linkFitR fr_batDrawsS rfl rfl
    (fun V => fr_headKeeps first further V) frW y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc

/-- **Under Cb.BCHKS46At: the library's written link AT THE DESCRIPTION's OWN DECISION is
round-by-round sound**, for the entry's language, at the library's own counts: fr_link_sound with
hdec gone. -/
theorem fr_link_sound_desc (hA : BCHKS46At GF GE) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (first further : TableKey) (xs : List PQ.XO) (r : (frS.lkR frZ).X0) (hs : P.set.samples = 1)
    (hS : P.S = recordRead.link) (hC : P.codes = recordRead.codes)
        (hpub : PubAt P frC recordRead.codes)
    (hopen : OpensAt P frC)
    (hK0 : first.fits recordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1)
    (hK1 : further.fits recordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        (fun V => (descOf P plan ok).run (first, further) V)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 r y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  fr_link_joh hA xs _ r fun y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc =>
    fr_yes_desc P plan ok first further xs r hs hS hC hpub hopen hK0 hK1 y m0 c0 m1 c1 m2 c2 m3 c3
        m4 c4 m5 c5 mA
      cA b hacc

/-! ## The small example -/

/-- **hsem of sr_link_joh at the description's own decision**: the conclusion of the library's
sr_yes to the letter; its premise hdec is gone. -/
theorem sr_yes_desc (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (first further : TableKey)
    (xs : List PQ.XO) (r : (srS.lkR srZ).X0) (hs : P.set.samples = 1)
        (hS : P.S = smallRecordRead.link)
    (hC : P.codes = smallRecordRead.codes) (hpub : PubAt P srC smallRecordRead.codes)
        (hopen : OpensAt P srC)
    (hK0 : first.fits smallRecordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1)
    (hK1 : further.fits smallRecordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2)
    (y : (srS.lkR srZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : srC.Bl)
    (hacc : (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        (fun V => (descOf P plan ok).run (first, further) V)).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, srC.trL b) = true) :
    srC.Acc (sumStmR srN 97
        (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
            c5).1).1
        (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
            c5).1).2
        (drawnE (srRd 5) cA))
      (srW m2.1) (srF m2.1) (srW m2.1) b := by
  obtain ⟨set, codes, S, stages⟩ := P
  simp only at hS hC
  subst hS
  subst hC
  obtain ⟨_, hmems, hE, hm0, hst, hf1, hk, hR, h3, hz, hfm, hfz⟩ := sr_groupFacts
  exact yes_in_field_desc srS 97 19 1 _ plan ok first further smallRecordRead.given.rounds (srRd 0)
      (srRd 1) (srRd 2)
    (srRd 3) (srRd 4) (srRd 5) srC xs batOk hs hpub hopen sr_h0 sr_headTrees sr_trees sr_len
    (rowShape smallRecordRead.link) (maskShape smallRecordRead.link) _ hmems hE hm0 _ hst hf1 hk hR
        h3 hz hfm hfz
    (by decide +kernel) sr_pads r hK0 hK1 sr_linkSizesR sr_linkFitR sr_batDrawsS rfl rfl
    (fun V => sr_headKeeps first further V) srW y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc

/-- **Under Cb.BCHKS46At: the library's written link AT THE DESCRIPTION's OWN DECISION is
round-by-round sound**, for the entry's language, at the library's own counts: sr_link_sound with
hdec gone. -/
theorem sr_link_sound_desc (hA : BCHKS46At GF GE) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (first further : TableKey) (xs : List PQ.XO) (r : (srS.lkR srZ).X0) (hs : P.set.samples = 1)
    (hS : P.S = smallRecordRead.link) (hC : P.codes = smallRecordRead.codes)
        (hpub : PubAt P srC smallRecordRead.codes)
    (hopen : OpensAt P srC)
    (hK0 : first.fits smallRecordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1)
    (hK1 : further.fits smallRecordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        (fun V => (descOf P plan ok).run (first, further) V)).Sound
      (fun _ y => srS.LangE2T srZ 524285 r y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  sr_link_joh hA xs _ r fun y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc =>
    sr_yes_desc P plan ok first further xs r hs hS hC hpub hopen hK0 hK1 y m0 c0 m1 c1 m2 c2 m3 c3
        m4 c4 m5 c5 mA
      cA b hacc

/-! ## Another file's premise H, to the letter -/

section
open OnBytes.Flat TypedOracleCompiler.Slice OnBytes.Tie

/-- The decision at an instance: the description's run at the two keys written of the instance. -/
def decDescFull (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (x : XE AnsT 29 1) : PQ.View →
    Bool :=
  fun V => (descOf P plan ok).run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x) V

def decDescSmall (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (x : XE AnsT 19 1) : PQ.View →
    Bool :=
  fun V => (descOf P plan ok).run (keysOfX srS.P.v 19 1 (anT srS.P.v 1) x) V

set_option maxRecDepth 100000 in
/-- **The premise H of another file's soundAt_full_of_joh
(Johnson/Flat/Dec/SoundAtOfWritten.lean:70-77), at decE := decDescFull P plan ok.** -/
theorem H_full (hA : BCHKS46At GF GE) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (hs : P.set.samples = 1) (hS : P.S = recordRead.link) (hC : P.codes = recordRead.codes)
    (hpub : PubAt P frC recordRead.codes) (hopen : OpensAt P frC) :
    ∀ x, (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
        (decDescFull P plan ok x)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recOf frS 29 1 (anT frS.P.v 1) x) y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  fun x =>
    fr_link_sound_desc hA P plan ok _ _ frD.xs (recOf frS 29 1 (anT frS.P.v 1) x) hs hS hC hpub
        hopen
    (fun _ _ => keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).1 _ rfl rfl Shapes.zFull_lg 0)
    (fun _ _ => keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).2 _ rfl rfl Shapes.zFull_lg 1)

set_option maxRecDepth 100000 in
/-- **The premise H of soundAt_small_of_joh (:115-122), at decE := decDescSmall P plan ok.** -/
theorem H_small (hA : BCHKS46At GF GE) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (hs : P.set.samples = 1) (hS : P.S = smallRecordRead.link)
        (hC : P.codes = smallRecordRead.codes)
    (hpub : PubAt P srC smallRecordRead.codes) (hopen : OpensAt P srC) :
    ∀ x, (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
        (decDescSmall P plan ok x)).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recOf srS 19 1 (anT srS.P.v 1) x) y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  fun x =>
    sr_link_sound_desc hA P plan ok _ _ srD.xs (recOf srS 19 1 (anT srS.P.v 1) x) hs hS hC hpub
        hopen
    (fun _ _ => keyHasR_keyOf (recOf srS 19 1 (anT srS.P.v 1) x).1 _ rfl rfl Shapes.zSmall_lg 0)
    (fun _ _ => keyHasR_keyOf (recOf srS 19 1 (anT srS.P.v 1) x).2 _ rfl rfl Shapes.zSmall_lg 1)

end

end Desc.K15

#print axioms Desc.K15.batOk
#print axioms Desc.K15.H_full
#print axioms Desc.K15.H_small
#print axioms Desc.K15.fr_yes_desc
#print axioms Desc.K15.fr_link_sound_desc
#print axioms Desc.K15.sr_yes_desc
#print axioms Desc.K15.sr_link_sound_desc
