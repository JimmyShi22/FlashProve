-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Traces.lean: the search for the integer m (Params.largestM), walked for every
test good that answers as named: one statement for each m that the sizing of a key of full size
finds.

Main names.
  trace‹m›: if good answers at the some fifteen numbers that the search tries as the premises say,
    then largestM good = m. For m = 91, 128, 138, 158, 167, 168, 182, 195, 201, 209, 210, 277, 291,
    292, 306, 341, 345, 420, 423, 449, 469, 470, 482, 489, 508, 509, 530.

Limits. good is a letter: no test is evaluated here. Nothing on soundness.

-/
import OnBytes.Params.Fit.TurnForward

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

theorem trace91 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = false)
    (h96 : good 96 = false)
    (h80 : good 80 = true)
    (h88 : good 88 = true)
    (h92 : good 92 = false)
    (h90 : good 90 = true)
    (h91 : good 91 = true) :
    largestM good = 91 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h96, h80, h88,
    h92, h90, h91]

theorem trace128 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = false)
    (h160 : good 160 = false)
    (h144 : good 144 = false)
    (h136 : good 136 = false)
    (h132 : good 132 = false)
    (h130 : good 130 = false)
    (h129 : good 129 = false) :
    largestM good = 128 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h160,
    h144, h136, h132, h130, h129]

theorem trace138 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = false)
    (h160 : good 160 = false)
    (h144 : good 144 = false)
    (h136 : good 136 = true)
    (h140 : good 140 = false)
    (h138 : good 138 = true)
    (h139 : good 139 = false) :
    largestM good = 138 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h160,
    h144, h136, h140, h138, h139]

theorem trace158 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = false)
    (h160 : good 160 = false)
    (h144 : good 144 = true)
    (h152 : good 152 = true)
    (h156 : good 156 = true)
    (h158 : good 158 = true)
    (h159 : good 159 = false) :
    largestM good = 158 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h160,
    h144, h152, h156, h158, h159]

theorem trace167 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = false)
    (h160 : good 160 = true)
    (h176 : good 176 = false)
    (h168 : good 168 = false)
    (h164 : good 164 = true)
    (h166 : good 166 = true)
    (h167 : good 167 = true) :
    largestM good = 167 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h160,
    h176, h168, h164, h166, h167]

theorem trace168 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = false)
    (h160 : good 160 = true)
    (h176 : good 176 = false)
    (h168 : good 168 = true)
    (h172 : good 172 = false)
    (h170 : good 170 = false)
    (h169 : good 169 = false) :
    largestM good = 168 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h160,
    h176, h168, h172, h170, h169]

theorem trace182 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = false)
    (h160 : good 160 = true)
    (h176 : good 176 = true)
    (h184 : good 184 = false)
    (h180 : good 180 = true)
    (h182 : good 182 = true)
    (h183 : good 183 = false) :
    largestM good = 182 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h160,
    h176, h184, h180, h182, h183]

theorem trace195 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = true)
    (h224 : good 224 = false)
    (h208 : good 208 = false)
    (h200 : good 200 = false)
    (h196 : good 196 = false)
    (h194 : good 194 = true)
    (h195 : good 195 = true) :
    largestM good = 195 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h224,
    h208, h200, h196, h194, h195]

theorem trace201 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = true)
    (h224 : good 224 = false)
    (h208 : good 208 = false)
    (h200 : good 200 = true)
    (h204 : good 204 = false)
    (h202 : good 202 = false)
    (h201 : good 201 = true) :
    largestM good = 201 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h224,
    h208, h200, h204, h202, h201]

theorem trace209 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = true)
    (h224 : good 224 = false)
    (h208 : good 208 = true)
    (h216 : good 216 = false)
    (h212 : good 212 = false)
    (h210 : good 210 = false)
    (h209 : good 209 = true) :
    largestM good = 209 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h224,
    h208, h216, h212, h210, h209]

theorem trace210 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = false)
    (h192 : good 192 = true)
    (h224 : good 224 = false)
    (h208 : good 208 = true)
    (h216 : good 216 = false)
    (h212 : good 212 = false)
    (h210 : good 210 = true)
    (h211 : good 211 = false) :
    largestM good = 210 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h192, h224,
    h208, h216, h212, h210, h211]

theorem trace277 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = false)
    (h320 : good 320 = false)
    (h288 : good 288 = false)
    (h272 : good 272 = true)
    (h280 : good 280 = false)
    (h276 : good 276 = true)
    (h278 : good 278 = false)
    (h277 : good 277 = true) :
    largestM good = 277 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h320, h288, h272, h280, h276, h278, h277]

theorem trace291 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = false)
    (h320 : good 320 = false)
    (h288 : good 288 = true)
    (h304 : good 304 = false)
    (h296 : good 296 = false)
    (h292 : good 292 = false)
    (h290 : good 290 = true)
    (h291 : good 291 = true) :
    largestM good = 291 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h320, h288, h304, h296, h292, h290, h291]

theorem trace292 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = false)
    (h320 : good 320 = false)
    (h288 : good 288 = true)
    (h304 : good 304 = false)
    (h296 : good 296 = false)
    (h292 : good 292 = true)
    (h294 : good 294 = false)
    (h293 : good 293 = false) :
    largestM good = 292 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h320, h288, h304, h296, h292, h294, h293]

theorem trace306 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = false)
    (h320 : good 320 = false)
    (h288 : good 288 = true)
    (h304 : good 304 = true)
    (h312 : good 312 = false)
    (h308 : good 308 = false)
    (h306 : good 306 = true)
    (h307 : good 307 = false) :
    largestM good = 306 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h320, h288, h304, h312, h308, h306, h307]

theorem trace341 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = false)
    (h320 : good 320 = true)
    (h352 : good 352 = false)
    (h336 : good 336 = true)
    (h344 : good 344 = false)
    (h340 : good 340 = true)
    (h342 : good 342 = false)
    (h341 : good 341 = true) :
    largestM good = 341 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h320, h352, h336, h344, h340, h342, h341]

theorem trace345 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = false)
    (h320 : good 320 = true)
    (h352 : good 352 = false)
    (h336 : good 336 = true)
    (h344 : good 344 = true)
    (h348 : good 348 = false)
    (h346 : good 346 = false)
    (h345 : good 345 = true) :
    largestM good = 345 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h320, h352, h336, h344, h348, h346, h345]

theorem trace420 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = false)
    (h416 : good 416 = true)
    (h432 : good 432 = false)
    (h424 : good 424 = false)
    (h420 : good 420 = true)
    (h422 : good 422 = false)
    (h421 : good 421 = false) :
    largestM good = 420 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h416, h432, h424, h420, h422, h421]

theorem trace423 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = false)
    (h416 : good 416 = true)
    (h432 : good 432 = false)
    (h424 : good 424 = false)
    (h420 : good 420 = true)
    (h422 : good 422 = true)
    (h423 : good 423 = true) :
    largestM good = 423 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h416, h432, h424, h420, h422, h423]

theorem trace449 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = true)
    (h480 : good 480 = false)
    (h464 : good 464 = false)
    (h456 : good 456 = false)
    (h452 : good 452 = false)
    (h450 : good 450 = false)
    (h449 : good 449 = true) :
    largestM good = 449 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h480, h464, h456, h452, h450, h449]

theorem trace469 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = true)
    (h480 : good 480 = false)
    (h464 : good 464 = true)
    (h472 : good 472 = false)
    (h468 : good 468 = true)
    (h470 : good 470 = false)
    (h469 : good 469 = true) :
    largestM good = 469 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h480, h464, h472, h468, h470, h469]

theorem trace470 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = true)
    (h480 : good 480 = false)
    (h464 : good 464 = true)
    (h472 : good 472 = false)
    (h468 : good 468 = true)
    (h470 : good 470 = true)
    (h471 : good 471 = false) :
    largestM good = 470 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h480, h464, h472, h468, h470, h471]

theorem trace482 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = true)
    (h480 : good 480 = true)
    (h496 : good 496 = false)
    (h488 : good 488 = false)
    (h484 : good 484 = false)
    (h482 : good 482 = true)
    (h483 : good 483 = false) :
    largestM good = 482 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h480, h496, h488, h484, h482, h483]

theorem trace489 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = true)
    (h480 : good 480 = true)
    (h496 : good 496 = false)
    (h488 : good 488 = true)
    (h492 : good 492 = false)
    (h490 : good 490 = false)
    (h489 : good 489 = true) :
    largestM good = 489 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h480, h496, h488, h492, h490, h489]

theorem trace508 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = true)
    (h480 : good 480 = true)
    (h496 : good 496 = true)
    (h504 : good 504 = true)
    (h508 : good 508 = true)
    (h510 : good 510 = false)
    (h509 : good 509 = false) :
    largestM good = 508 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h480, h496, h504, h508, h510, h509]

theorem trace509 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = false)
    (h384 : good 384 = true)
    (h448 : good 448 = true)
    (h480 : good 480 = true)
    (h496 : good 496 = true)
    (h504 : good 504 = true)
    (h508 : good 508 = true)
    (h510 : good 510 = false)
    (h509 : good 509 = true) :
    largestM good = 509 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h384,
    h448, h480, h496, h504, h508, h510, h509]

theorem trace530 (good : Nat → Bool)
    (h3 : good 3 = true)
    (h4 : good 4 = true)
    (h8 : good 8 = true)
    (h16 : good 16 = true)
    (h32 : good 32 = true)
    (h64 : good 64 = true)
    (h128 : good 128 = true)
    (h256 : good 256 = true)
    (h512 : good 512 = true)
    (h1024 : good 1024 = false)
    (h768 : good 768 = false)
    (h640 : good 640 = false)
    (h576 : good 576 = false)
    (h544 : good 544 = false)
    (h528 : good 528 = true)
    (h536 : good 536 = false)
    (h532 : good 532 = false)
    (h530 : good 530 = true)
    (h531 : good 531 = false) :
    largestM good = 530 := by
  simp [largestM, firstGood, growGood, lastGood, h3, h4, h8, h16, h32, h64, h128, h256, h512, h1024,
    h768, h640, h576, h544, h528, h536, h532, h530, h531]

end OnBytes.Params

#print axioms OnBytes.Params.trace91
#print axioms OnBytes.Params.trace128
