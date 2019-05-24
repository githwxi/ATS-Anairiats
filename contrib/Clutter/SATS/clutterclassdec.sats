(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2009-2010 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2010
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

staload GOBJ = "contrib/glib/SATS/glib-object.sats"
stadef GObject = $GOBJ.GObject
stadef GInitiallyUnowned = $GOBJ.GInitiallyUnowned
stadef GInterface = $GOBJ.GInterface

(* ****** ****** *)

//
// GObject
//
classdec ClutterActor : GInitiallyUnowned
  classdec ClutterGroup : ClutterActor
    classdec ClutterStage : ClutterGroup
  classdec ClutterRectangle : ClutterActor
  classdec ClutterTexture : ClutterActor
    classdec ClutterCairoTexture : ClutterTexture
  classdec ClutterClone : ClutterActor
  classdec ClutterText : ClutterActor
  classdec ClutterBox : ClutterActor
  classdec ClutterAlpha : GObject
  classdec ClutterPath : GObject
  classdec ClutterInterval : GObject
  classdec ClutterLayoutManager : GObject
    classdec ClutterFixedLayout : ClutterLayoutManager
    classdec ClutterBinLayout : ClutterLayoutManager
    classdec ClutterFlowLayout : ClutterLayoutManager
    classdec ClutterBoxLayout : ClutterLayoutManager
classdec ClutterActorMeta : GInitiallyUnowned
  classdec ClutterAction : ClutterActorMeta
  classdec ClutterConstraint : ClutterActorMeta
  classdec ClutterEffect : ClutterActorMeta
classdec ClutterTimeline : GObject
classdec ClutterBehaviour : GObject
  classdec ClutterBehaviourDepth : ClutterBehaviour
  classdec ClutterBehaviourEllipse : ClutterBehaviour
  classdec ClutterBehaviourOpacity : ClutterBehaviour
  classdec ClutterBehaviourPath : ClutterBehaviour
  classdec ClutterBehaviourRotate : ClutterBehaviour
  classdec ClutterBehaviourScale : ClutterBehaviour
classdec ClutterScript : GObject
classdec ClutterModel : GObject
  classdec ClutterListModel : ClutterModel
classdec ClutterModelIter : GObject
classdec ClutterScore : GObject
classdec ClutterShader : GObject
classdec ClutterChildMeta : GObject
  classdec ClutterLayoutMeta : ClutterChildMeta
classdec ClutterAnimation : GObject
classdec ClutterStageManager : GObject
classdec ClutterBindingPool : GObject
classdec ClutterInputDevice : GObject
classdec ClutterDeviceManager : GObject
classdec ClutterAnimator : GObject

//
// GInterface
//
classdec ClutterScriptable : GInterface
classdec ClutterContainer : GInterface
classdec ClutterMedia : GInterface
classdec ClutterAnimatable : GInterface

(* ****** ****** *)

(* end of [clutterclassdec.sats] *)
