-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/K3FormsLayers.lean

«FORMS AGAINST KEYS», THE LAYERS.
Nothing on hiding. No property of a release.
WHAT STANDS ON THE TWO SIDES. The table of joints' key vectors at a layers' link (Johnson/Desc/First/Look/K3CallerLay.lean: layLay_K)
are THE LIBRARY's keyVec at the reference sizes DF, the reference tables tbRef, the reference layout kRef of the weights, the scales
sclOf h sc g 4, the cells cellsOf DF (cellsAt y ·), the layers' matrices layerR ppref kRef ·. The honest lookup runs on G.kvG
(OnBytes/Tie/Pv/Lookup/Ends/G.lean; Honest/K3/Law/KeysAreKvG.lean: keysG).
HERE, BY CALLS: the two are one vector, at every call and every index below 2 ^ aC DF c, the padding included:
  layers_key_vector_is_kvG_of_lines: at letters, under the public premises of Alg.calls_of_layerKeys (Johnson/Road/Lane5KeysIffG.lean),
    after its proof: ties_of_lines · agreeT_of_ropeOK · callFits_of_layout · padG_of_isLut · keyVec_kvG.
  layers_key_vector_is_kvG_in_scope: in the goals' scope, g < 12, AT EVERY LIST Mz OF INTEGER MATRICES AND EVERY MATRIX Wi: the premises
    paid as in forInG_of_keys_in_scope (Johnson/Goal/HonestTrace/FullInScope.lean:590).
  layers_key_extension_is_kvG_in_scope: so their extensions at any point are one.
NOT HERE: that the verifier's FORMS (Env.line, joinPart, the panels) are worth these vectors' extensions: the library's alg_line | alg_call
(affine parts) and whole_lib | capstone (Johnson/Road/FormsKeysCaller.lean): K4's matter.
-/
import Johnson.Goal.HonestTrace.FullInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

namespace K3Forms

open OnBytes.Ends
open OnBytes.Road.L5
open OnBytes.Model (Seg CallD Call WsShape wsLayOf)
open OnBytes.Model.Layer (Env Lay Shape Scales Reads TableAsk TableAt Ten layout scalesHeld readsOf
  layTables tableAsks)
open Inst.Model (Scl Tables Mat ppref tbRef AcceptancePolicy)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell Fam LW fams used aC lut keyVec layerR)

section Letters

variable {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ}
  {rd : OnBytes.Model.Layer.Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **The library's key vector of a call, at the casts of Mz and Wi, is G.lean's kvG**, under public premises alone. -/
theorem layers_key_vector_is_kvG_of_lines (hy : layout h pc = .ok P.y) (S : Switches h)
    (hs : scalesHeld h P.sc = .ok ()) (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) (Zd : Sized h Dim.ref)
    (hp4 : h.p4 = true) (hev : h.dh % 2 = 0)
    (hmats : ∀ (n : String) (Tn : Ten), P.y.T_ n = some Tn → Tn.mat < 4)
    (hT : P.y.T = Dim.ref.T) {s : WsShape} (ZW : SizedW s ppref)
    (hW : wsLayOf s true kRef = .ok P.wsLay)
    (hgL : ∀ l < Dim.ref.nl, g * P.y.Lam + l < ppref.layers)
    (hrope : ropeOK P Dim.ref tbRef (g * P.y.Lam) = true)
    (h8 : P.y.calls.size = 8)
    (hn : ∀ (cc : Fin 8) (cd : CallD), P.y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used Dim.ref cc))
    (hw : ∀ cd ∈ P.y.calls, ∃ wg, (envG P g r.1).weighedOf cd = some wg)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧ Hd.IsLut c0 (lut tbRef cc))
    (Mz : Mats ℤ) (Wi : Mat) (c : Fin 8) (X : ℕ) (hX : X < 2 ^ aC Dim.ref c) :
    keyVec (scl := sclOf h P.sc g 4) Dim.ref
        (cellsOf Dim.ref (cellsAt P.y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))) tbRef (4 * g)
        (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
      G.kvG P g (cellMW Mz Wi) c.val X := by
  have hch : 0 < ppref.ch := by decide
  obtain ⟨hLam, hffe, Ti, Wt, Aw⟩ := ties_of_lines (D := Dim.ref) rfl rfl hch hy S hs hg hrd hl Zd
    hp4 hev hmats ZW hW hgL Mz Wi
  letI : Scl := sclOf h P.sc g 4
  have B := agreeT_of_ropeOK hrope
  have hc8 : c.val < P.y.calls.size := by
    rw [h8]
    exact c.isLt
  obtain ⟨cd, hcq⟩ : ∃ cd, P.y.calls[c.val]? = some cd := ⟨_, Array.getElem?_eq_getElem hc8⟩
  have hmem : cd ∈ P.y.calls := Array.mem_of_getElem? hcq
  obtain ⟨wg, hwg⟩ := hw cd hmem
  obtain ⟨C, HS⟩ := callFits_of_layout (v := envG P g r.1) hy S Zd hmem (hn c cd hcq) (hfl c) hwg
  obtain ⟨c0, hc0, hLc⟩ := hL c
  have hcdP : P.y.calls.getD c.val default = cd := by
    rw [Array.getD_eq_getD_getElem?, hcq]
    rfl
  have e := keyVec_kvG Ti Wt Aw B hffe hch C HS hcdP hT (padG_of_isLut hc0 hLc) X hX
  rw [cellsOf_congr Dim.ref (cG_cellsAt P (M := fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
    (fun _ _ _ => rfl)), hLam, Nat.mul_comm g 4] at e
  exact e

end Letters

section Scope

open Meaning Meaning.P34 OnBytes.Model
open OnBytes.Model.Verify (publicOf layerShape)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **IN THE GOALS' SCOPE, g < 12, AT EVERY Mz AND Wi: the table of joints' key vector of call c is kvG**, at every index below
2 ^ aC DF c. -/
theorem layers_key_vector_is_kvG_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12)
    (Mz : Mats ℤ) (Wi : Mat) (c : Fin 8) (n : ℕ) (hn : n < 2 ^ aC DF c) :
    keyVec (scl := sclOf (layerShape X.P) X.layers.sc g 4) DF
        (cellsOf DF (cellsAt X.y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))) tbRef (4 * g)
        (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c n =
      G.kvG X.layers g (cellMW Mz Wi) c.val n := by
  obtain ⟨mats, r, hl⟩ := hl_in_scope hZ hR h g
  obtain ⟨hy, S, hs, hrd, Zd, -, hN, hfl, Zw, -, hlw, h4⟩ := pub34_public hZ hR h
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have hsh := shape_in_scope hZ hR h
  have hLam : X.y.Lam = 4 := by
    rw [(laid_of_layout hy S.p3).2.Lam, shape_of_public h, hsh]
    rfl
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  exact layers_key_vector_is_kvG_of_lines (P := pubAt X X.layers.tokv) (rd := X.layers.rd) hy S hs
    (by show g < X.y.NGr; rw [B.groups]; exact hg) hrd hl Zd h4
    (by rw [show (layerShape X.P).dh = 128 from A.num 7]) (hmats_of_layout hy S.p3)
    (by
      show X.y.T = DF.T
      rw [(laid2_of_layout hy).T, shape_of_public h, hsh]
      rfl)
    Zw hlw
    (fun l hl4 => by
      show g * X.y.Lam + l < 48
      have : l < 4 := hl4
      rw [hLam]
      omega)
    (Rope.ropeOK_in_scope hZ hR h hg) h8
    (fun cc cd hcd => by
      have e := line_at hN cc
      have eg : X.y.calls.getD cc.val default = cd := by
        have hq : cc.val < X.y.calls.size := by rw [h8]; exact cc.isLt
        have hcd' : X.y.calls[cc.val]? = some cd := hcd
        rw [Array.getElem?_eq_getElem hq] at hcd'
        simp [Array.getD, hq, Option.some.inj hcd']
      rw [eg] at e
      exact e)
    hfl (fun cd hcd => weighed_in_scope hZ hR h cd hcd)
    (fun cc => by
      obtain ⟨c0, a, b, -⟩ := hL_in_scope hZ hR h cc
      exact ⟨c0, a, b⟩) Mz Wi c n hn

/-- Their extensions at any point are one. -/
theorem layers_key_extension_is_kvG_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12)
    (Mz : Mats ℤ) (Wi : Mat) (c : Fin 8) (ζ : ℕ → Cb.Gl.E) :
    Blocks.ext (aC DF c)
        (keyVec (scl := sclOf (layerShape X.P) X.layers.sc g 4) DF
          (cellsOf DF (cellsAt X.y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))) tbRef (4 * g)
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c) ζ =
      Blocks.ext (aC DF c) (G.kvG X.layers g (cellMW Mz Wi) c.val) ζ :=
  Blocks.ext_congr (fun n hn => layers_key_vector_is_kvG_in_scope hZ hR h hg Mz Wi c n hn) ζ

end Scope

end K3Forms

end OnBytes.Road.Alg

#print axioms OnBytes.Road.Alg.K3Forms.layers_key_vector_is_kvG_of_lines
#print axioms OnBytes.Road.Alg.K3Forms.layers_key_vector_is_kvG_in_scope
#print axioms OnBytes.Road.Alg.K3Forms.layers_key_extension_is_kvG_in_scope
