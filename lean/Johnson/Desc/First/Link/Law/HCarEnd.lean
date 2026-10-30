-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
(HFOfEnd.lean: hH
is asked at the state behind, under «the way in answers».) Johnson/Desc/First/Link/Law/HCarEnd.lean:
  **hCar FROM K10's LAW's OWN END (`K10EndS`,
Johnson/Desc/First/Close/Law/GoodOf.lean) AND THE TABLE's ITEM «carry» BEHIND THE CLOSING ⊢
`CarriedAt … (faK10 … z a) (rdBK a'.1).1.rows`**, at the typed group of a list at the program's own
layout (`groupLayK cs lo s e kb hM hZ`), the names `namesOf … no` and the fresh mask's word mW b :=
mWRaw … (strsOf F b.2) tree skip aF. The join of `hCar_ren` (HCarRen.lean) with `hF_of_end`
(HFOfEnd.lean): K10EndS's own clauses give «a'.1 = wrK a.1 …» and «a'.2 is the piece's strings
behind a.2». A theorem. It changes no other file.

  `hCar_end`: K10EndS … (faK10 … z) a a' · carryAtZ Z lay m (z, a'.1) (strsOf F a'.2) w · what is
    asked of the switch's typed row (hr) · `hF_of_end`'s premises · the second half of CarriedAt
    (h2) ⊢ CarriedAt ….
AGAINST THE FIELD hCar OF THE CLOSING's FILES' STRUCTURE OF WHAT ITS ASSEMBLED LAW ASKS (K10Heavy):
NOT THAT FIELD: hCar_heavy (HCarHeavy.lean) IS, AND CALLS THIS THEOREM. WHAT PARTS THE TWO:
(1) The field's hypothesis behind the closing is the table's relation at the
items that go out; here the item «carry» stands as the closed constant has it (carryAtZ): nothing
here ties the two. (2) The field has the names and the fresh mask's word as letters; here they are
the two terms. (3) The field also gives what is known in front (its letter X) and K10's law's
condition in front; neither is spent here: the premises in front stand free.
Limits. EVERY PREMISE BUT K10EndS AND THE ITEM STANDS AS IN HFOfEnd.lean AND HCarRen.lean; NONE IS
SHOWN AT A REACHED STATE HERE (HCarAll.lean lays most of them in, from the head and rowsRead; its
head lists what is left). IT PROVES ONE OF CarriedAt's TWO HALVES: THE SECOND IS ITS PREMISE h2,
WORD FOR WORD. THE ITEM «carry» (hC) IS A PREMISE: THAT IT HOLDS AT ANY STATE IS NO THEOREM's END;
of what it says only «near the open word» and «the claim» are spent. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HCarRen
import Johnson.Desc.First.Link.Law.HFOfEnd
import Johnson.Desc.First.Close.Law.GoodOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker Cb Iop IOR Johnson.Top.H Johnson.Pack
open Johnson.G OnBytes.Tie.Pv.Fold OnBytes.Flat KObj Run
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb.Pv
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K2Caller (SeatFitAt doorZ carryAtZ)
open VerifiableInference.Desc.First.Close (groupLayK namesOf posOf ShapesAre AgreesWith layAt sizesM
  sizesZ rdBK wrK CarriedAt faK10 SbV slV ZV K10EndS pieceOn Par)
open _root_.Tw.K2 (switchNotices)

/-- **hCar, FROM K10's LAW's OWN END AND THE ITEM «carry» BEHIND.** -/
theorem hCar_end (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    {Xi : Type} (G : FileDescription Xi)
    (seat : Fin lo.length → ℕ × ℕ) (no : Fin lo.length → ℕ)
    (keep : (sigOf cs lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
    (pull : ((groupLayK cs lo s e kb hM hZ).Sh.Cin.J → GE) →
      (groupLayK cs lo s e kb hM hZ).G.C.J → GE) (n : ℕ)
    (num : (groupLayK cs lo s e kb hM hZ).G.Row B ≃ Fin n)
    (fx : Fin (((groupLayK cs lo s e kb hM hZ).Sh.fold (SbV (groupLayK cs lo s e kb hM hZ) B)
      (slV (groupLayK cs lo s e kb hM hZ) pull)
      (ZV (groupLayK cs lo s e kb hM hZ) n num)).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
      (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
      (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp).Msg × Wp))
    (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
    (w₁ : LdBrW (groupLayK cs lo s e kb hM hZ).G ((groupLayK cs lo s e kb hM hZ).sizeB keep
      (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
      (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp Wp)
    (L : List (BatFoldCaller GE)) {Pz Wt : Type}
    (smp : Pz × First.S → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
    (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame} (Z : ProofFile.Pub)
    (lay : ByteArray) (m : ℕ) (z : Pz) (a a' : First.S × F.E.Str) (w : Wt) (D : WholeD)
    (hW : ProofFile.wholeAt Z = some D) (dB dE dR : RDT) {Cl W : Type} (Pr : Par)
    (b : Block First.S Cl) (base : ℕ)
    (ext : First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate
      (Yc ((groupLayK cs lo s e kb hM hZ).foldCaller keep (SbV (groupLayK cs lo s e kb hM hZ) B)
      (slV (groupLayK cs lo s e kb hM hZ) pull) (ZV (groupLayK cs lo s e kb hM hZ) n num) fx A₀ bC
      bZ w₀ w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate
      (Yc ((groupLayK cs lo s e kb hM hZ).foldCaller keep (SbV (groupLayK cs lo s e kb hM hZ) B)
      (slV (groupLayK cs lo s e kb hM hZ) pull) (ZV (groupLayK cs lo s e kb hM hZ) n num) fx A₀ bC
      bZ w₀ w₁)).k dR)))
    (tree tnF skip aF : ℕ)
    (hEnd : K10EndS (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) keep pull n
      num fx
      A₀ bC bZ w₀ w₁ L dB dE dR Pr b base ext err
      (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) keep pull
        n num
        fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀
        (fun b : First.S × F.E.Str => mWRaw cs lo (memMain lo) s e
          (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val) hM hZ
          (fun a => kb a.1 = true) (strsOf F b.2) tree skip aF) z) a a')
    (hC : carryAtZ Z lay m (z, a'.1) (strsOf F a'.2) w)
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → (∃ t₀, s = stageOf r.g t₀) ∧
      (∀ n, keptRowsAt r.lo r.mem r.kp n =
        keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n) ∧ r.rad ≤ e)
    (hH : ∀ t, doorZ Z m a'.1 = some t → (ProofFile.pAtK2 Z m).stands = .head →
      ∀ b, a'.1.here ≠ .head b)
    (hgood : (groupLayK cs lo s e kb hM hZ).Good) {T : Statement} {Gr : Group}
    (H : ShapesAre T Gr lo kb no) (hLm : a'.1.live.frame.rows.layout.members = Gr.members)
    (hLk : a'.1.live.frame.rows.layout.kept = Gr.kept)
    (hA : AgreesWith lo kb a'.1.live.frame.rows.layout) (hm : a'.1.live.frame.rows.masks = 2)
    (hγ : a'.1.live.frame.rows.gamma.length = s.h + s.g)
    (hk : a'.1.live.frame.rows.layout.k = s.h + s.g) (hh : a'.1.live.frame.rows.layout.h = s.h)
    (hord : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → ∀ i : Fin lo.length, memMain lo i →
      kb i = true → (keptNosOf lo kb)[r.kept.idxOf i.val]? = some (posOf lo i))
    (hS : ∀ b : {i // memMain lo i}, SeatFitAt G cs lo seat b.1)
    (hSh : ∀ b : {i // memMain lo i}, ShownAt G cs lo seat (strsOf F a.2) b.1)
    (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (hPB : ∀ b : {i // memMain lo i},
      planPubB G a.1 Lp (no b.1) (seat b.1) (aOf cs (lo.get b.1).1) = true)
    (hPl : ∀ b : {i // memMain lo i}, Lp.places[no b.1]? = some (seat b.1))
    (hsD : ∀ b : {i // memMain lo i}, (seat b.1).1 < D.t₁) (hsB : ∀ i, (seat i).1 < base)
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook
      (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree a.1 = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats Lp a.1 = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits a.1 = true)
    (hpos : 2 ^ s.C.a ≤ 2 ^ (ProofFile.pAtK2 Z m).logN)
    (hfo : a'.1.live.frame.rows.fresh < a.1.book.place.size)
    (hfL : Lp.places[a'.1.live.frame.rows.fresh]? = some (tree, tnF)) (shF0 : TreeShape)
    (hfs : Lp.shapes[tree]? = some shF0) (hfa : shF0.logN = aF) (htD : tree < D.t₁)
    (htB : tree < base)
    (hfskip : shF0.mainWidth + (shF0.maskSymbols.extract 0 tnF).foldl (· + ·) 0 = skip)
    (hFr : ∀ t fx', doorZ Z m a'.1 = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' →
      (∃ B, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx'.st t.book t.roots
        (switchNotices fx'.T fx'.others) = some B) ∧
      (∀ b : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx').oracles[no b.1]? = some xo ∧
        xo.shape = (lo.get b.1).1) ∧
      (∃ xoF, (First.K2.skelOf fx').oracles[a'.1.live.frame.rows.fresh]? = some xoF ∧
        xoF.shape.maskRows = 2 ^ s.h) ∧
      keptCount a'.1.live.frame.rows.layout
        (fun w => ((First.K2.skelOf fx').oracles.getD
          (a'.1.live.frame.rows.layout.members.getD w 0) default).shape.mainRows)
        (List.range a'.1.live.frame.rows.layout.members.size) =
        a'.1.live.frame.rows.keptRows)
    (h2 : ∃ (zz : (ZV (groupLayK cs lo s e kb hM hZ) n num).D)
      (v : ((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
        (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
        (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp).Wit × Wp),
      (((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
        (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
        (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp).over A₀).relR
        ((batX ((groupLayK cs lo s e kb hM hZ).foldCaller keep
            (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
            (ZV (groupLayK cs lo s e kb hM hZ) n num) fx A₀ bC bZ w₀ w₁)
          (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) keep
            pull n num fx
            A₀ bC
            bZ w₀ w₁ L smp σ₀ st₀ e₀
            (fun b : First.S × F.E.Str => mWRaw cs lo (memMain lo) s e
              (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val) hM hZ
              (fun a => kb a.1 = true) (strsOf F b.2) tree skip aF) z a).1 zz).2,
          ((ldBrG (groupLayK cs lo s e kb hM hZ).G ((groupLayK cs lo s e kb hM hZ).sizeB keep
            (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
            (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp E₀).map
            (e₀, wordsOf G cs lo seat (strsOf F a.2))).2) v) :
    CarriedAt (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) keep
       (SbV (groupLayK cs lo s e kb hM hZ) B)
      (slV (groupLayK cs lo s e kb hM hZ) pull) (ZV (groupLayK cs lo s e kb hM hZ) n num) fx
      A₀ bC bZ w₀ w₁ L
      (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) keep pull
        n num
        fx A₀ bC bZ
        w₀ w₁ L smp σ₀ st₀ e₀
        (fun b : First.S × F.E.Str => mWRaw cs lo (memMain lo) s e
          (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val) hM hZ
          (fun a => kb a.1 = true) (strsOf F b.2) tree skip aF) z a)
      (rdBK a'.1).1.rows := by
  obtain ⟨⟨τ, e1, -, -⟩, ew, -⟩ := hEnd
  have hst : ∀ j x, j < base → (strsOf F a'.2).col j x = (strsOf F a.2).col j x :=
    fun j x hj => imp_stays (pieceOn (W := W) (F := F) b base dB dE dR _ ext err) e1 j x hj
  exact hCar_ren cs lo s e kb hM hZ G seat _ keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀ Z
    lay m z a a'.1 (strsOf F a'.2) w (fun b => no b.1) (fun b => posOf lo b.1) _ _ hr
    (hF_of_end cs lo s e kb hM hZ no G seat Z lay m D hW a a' _ _ ew base hst hH hgood H hLm hLk hA
      hm hγ hk hh hord hS hSh Lp hPB hPl hsD hsB hIn hSe hFi hpos tree tnF skip aF hfo hfL shF0 hfs
      hfa htD htB hfskip hFr)
    (fun i x => hst _ x (hsB i)) hC h2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hCar_end
