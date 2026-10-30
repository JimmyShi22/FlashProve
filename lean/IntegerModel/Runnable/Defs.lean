-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/Defs.lean: the renamings between the library's records
(Inst/Model/Program.lean) and the array program's
(IntegerModel/Runnable/ArrayModel.lean), and the conditions on sizes and tables.
Definitions, and four short lemmas: the shapes do not depend on the scales; the renamed records
agree with their originals.
-/
import Inst.Model.Program
import IntegerModel.Runnable.ArrayNext

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

/-! ## The renamings: the library's records as the program's records.  No arithmetic: fields are copied. -/

/-- the sizes; the program's window limit Tmax is an argument of its own (only ArrayProgram.next
reads it) -/
def shapeOf (P : Params) (Tmax : ℕ) : ArrayProgram.Shape :=
  { T := Tmax, V := P.V, layers := P.layers, d := P.d, heads := P.nq, kvHeads := P.nkv,
    headDim := P.ch, ffDense := P.f, ffExpert := P.fe, experts := P.nexp }
def normOf (n : NormPar) : ArrayProgram.Norm := { M := n.M, K := n.K, eps := n.eps }
/-- expRows is not copied: the program has it with its tables (TabRel.rows) -/
def scalesOf (s : LayerScale) : ArrayProgram.LayerScales :=
  { kq := s.kq, kk := s.kk, kv := s.kv, ko := s.ko, kg := s.kg, ku := s.ku, kd := s.kd, kr := s.kr,
    kgR := s.kg', kuR := s.ku', norm1 := normOf s.n1, norm2 := normOf s.n2, sh := s.sh }
def settingsOf (κ : ℕ → LayerScale) (nf : NormPar) : ArrayProgram.Settings :=
  { layer := fun L => scalesOf (κ L), final := normOf nf }
def layerOf (w : LayerW) : ArrayProgram.LayerWeights :=
  { Wq := w.Wq, Wk := w.Wk, Wv := w.Wv, Wo := w.Wo, Wgate := w.Wg, Wup := w.Wu, Wdown := w.Wd,
    Wrouter := w.Wr, Egate := w.Eg, Eup := w.Eu, Edown := w.Ed }
def weightsOf (w : Weights) : ArrayProgram.Weights :=
  { layer := fun L => layerOf (w.layer L), embedding := w.Emb, head := w.H }
/-- the scales that a Params carries for all layers (the library runs layer L at "P.at (κ L)") -/
def lsOf (P : Params) : ArrayProgram.LayerScales := scalesOf P.scale

/-! ## What a run is given: records that agree with the library's inside the shapes

Inside the shapes means: the layers below P.layers; each matrix's rows and columns; the router's and
the experts' matrices and the three shifts kr, kgR, kuR only in the layers with experts. Outside
them nothing is required. So it follows from the theorems of IntegerModel/Runnable/Main.lean and
AtModelSizes.lean, under their hypotheses, that the program's output does not depend on what is
there.
(The tables are different: TabRel below requires SiLU, sigmoid and exp as functions on all integers,
cos and sin at all positions and angles.)
-/

/-- The program's weights W of layer L are the library's w at every position inside the shapes. A
dense layer has f hidden units; a layer with experts has fe shared ones, a router and nexp experts
of fe units. -/
structure SameLayer (P : Params) (L : ℕ) (W : ArrayProgram.LayerWeights) (w : LayerW) : Prop where
  Wq : ∀ j < P.d, ∀ c < P.nq * P.ch, W.Wq j c = w.Wq j c
  Wk : ∀ j < P.d, ∀ c < P.nkv * P.ch, W.Wk j c = w.Wk j c
  Wv : ∀ j < P.d, ∀ c < P.nkv * P.ch, W.Wv j c = w.Wv j c
  Wo : ∀ j < P.nq * P.ch, ∀ c < P.d, W.Wo j c = w.Wo j c
  Wg : ∀ j < P.d, ∀ c < (if hasExperts L then P.fe else P.f), W.Wgate j c = w.Wg j c
  Wu : ∀ j < P.d, ∀ c < (if hasExperts L then P.fe else P.f), W.Wup j c = w.Wu j c
  Wd : ∀ j < (if hasExperts L then P.fe else P.f), ∀ c < P.d, W.Wdown j c = w.Wd j c
  Wr : hasExperts L → ∀ j < P.d, ∀ e < P.nexp, W.Wrouter j e = w.Wr j e
  Eg : hasExperts L → ∀ e < P.nexp, ∀ j < P.d, ∀ c < P.fe, W.Egate e j c = w.Eg e j c
  Eu : hasExperts L → ∀ e < P.nexp, ∀ j < P.d, ∀ c < P.fe, W.Eup e j c = w.Eu e j c
  Ed : hasExperts L → ∀ e < P.nexp, ∀ j < P.fe, ∀ c < P.d, W.Edown e j c = w.Ed e j c

structure SameWeights (P : Params) (W : ArrayProgram.Weights) (w : Weights) : Prop where
  layer : ∀ L < P.layers, SameLayer P L (W.layer L) (w.layer L)
  emb : ∀ a < P.V, ∀ j < P.d, W.embedding a j = w.Emb a j
  head : ∀ j < P.d, ∀ v < P.V, W.head j v = w.H j v

/-- The program's scales sc of layer L are the library's k. The router's shift and the routed
expert's two shifts are required only in a layer with experts. -/
structure SameScales (L : ℕ) (sc : ArrayProgram.LayerScales) (k : LayerScale) : Prop where
  kq : sc.kq = k.kq
  kk : sc.kk = k.kk
  kv : sc.kv = k.kv
  ko : sc.ko = k.ko
  kg : sc.kg = k.kg
  ku : sc.ku = k.ku
  kd : sc.kd = k.kd
  norm1 : sc.norm1 = normOf k.n1
  norm2 : sc.norm2 = normOf k.n2
  sh : sc.sh = k.sh
  kr : hasExperts L → sc.kr = k.kr
  kgR : hasExperts L → sc.kgR = k.kg'
  kuR : hasExperts L → sc.kuR = k.ku'

structure SameSettings (P : Params) (st : ArrayProgram.Settings)
    (κ : ℕ → LayerScale) (nf : NormPar) : Prop where
  layer : ∀ L < P.layers, SameScales L (st.layer L) (κ L)
  final : st.final = normOf nf

/-- SameLayer passes from P to P.at s: the shapes are those of P whatever the scales -/
theorem SameLayer.at {P : Params} {L : ℕ} {W : ArrayProgram.LayerWeights} {w : LayerW}
    (h : SameLayer P L W w) (s : LayerScale) : SameLayer (P.at s) L W w :=
  ⟨h.Wq, h.Wk, h.Wv, h.Wo, h.Wg, h.Wu, h.Wd, h.Wr, h.Eg, h.Eu, h.Ed⟩

theorem sameLayer_of (P : Params) (L : ℕ) (w : LayerW) : SameLayer P L (layerOf w) w :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
theorem sameWeights_of (P : Params) (w : Weights) : SameWeights P (weightsOf w) w :=
  ⟨fun L _ => sameLayer_of P L (w.layer L), fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
theorem sameSettings_of (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) :
    SameSettings P (settingsOf κ nf) κ nf :=
  ⟨fun _ _ =>
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩,
    rfl⟩

/-- The program's one set of tables t compared with the library's tables tb of layer L and that
layer's number of rows in use of the table exp (expRows). The program has the rotary rule in its
code (off in the layers L % 4 = 3); the library has it in its tables C, S, which take the layer. -/
structure TabRel (t : ArrayProgram.Tables) (tb : Tables) (L : ℕ) (rows : ℤ) : Prop where
  silu : t.silu = tb.SILU
  sigm : t.sigmoid = tb.SIGM
  exp : t.exp = tb.Exp
  rows : t.expRows = rows
  cos : ∀ i j, (if ArrayProgram.hasRotary L = true then t.cos i j else 2 ^ 12) = tb.C L i j
  sin : ∀ i j, (if ArrayProgram.hasRotary L = true then t.sin i j else 0) = tb.S L i j

/-- what is asked of the sizes -/
structure Good (P : Params) : Prop where
  /-- A head has an even number of channels. Otherwise the rotary step pairs a head's last entry
with the entry after it. At the end of the query row the program then reads outside its array, and
the library the first key entry; at the end of the key row the library reads an entry
beyond the keys. -/
  ch : 2 ∣ P.ch
  /-- every query head's key/value head exists: else the program can read outside its arrays of keys
and values -/
  kv : 0 < P.nkv ∧ P.nkv ∣ P.nq
  /-- there is an expert: else the program reads entry 0 of an empty array of router logits -/
  nexp : 0 < P.nexp

end IntegerModel.Runnable
