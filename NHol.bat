:: This batch file loads the NHol interactive environment into the
:: latest version of F# Interactive (FSI) available on this machine.

@echo off
setlocal enabledelayedexpansion

:: Get location of required dll: NHol.dll
set NHOL_RELATIVE=NHol\bin\Debug\NHol.dll
set "NHOL_ABSOLUTE=%~dp0%NHOL_RELATIVE%"

:: Variables which hold paths to various versions of F# Interactive.
set FSI_30= "C:\Program Files (x86)\Microsoft SDKs\F#\3.0\Framework\v4.0\fsi.exe"
set FSI_20= "C:\Program Files (x86)\Microsoft F#\v4.0\fsi.exe"

:: Set variables which hold command-line arguments to be passed to F# Interactive.
set fsi_args= --lib:NHol^
  fsi_ver^
  --define:DEBUG^
  --define:TRACE^
  --define:USE^
  --use:init.fsx^
  --use:Logging.fs^
  --use:system.fs^
  --use:lib.fs^
  --use:fusion.fs^
  --use:basics.fs^
  --use:nets.fs^
  --use:printer.fs^
  --use:preterm.fs^
  --use:parser.fs^
  --use:equal.fs^
  --use:bool.fs^
  --use:drule.fs^
  --use:tactics.fs^
  --use:itab.fs^
  --use:simp.fs^
  --use:theorems.fs^
  --use:ind_defs.fs^
  --use:class.fs^
  --use:trivia.fs^
  --use:canon.fs^
  --use:meson.fs^
  --use:quot.fs^
  --use:pair.fs^
  --use:nums.fs^
  --use:recursion.fs^
  --use:arith.fs^
  --use:wf.fs^
  --use:calc_num.fs^
  --use:normalizer.fs^
  --use:grobner.fs^
  --use:ind_types.fs^
  --use:lists.fs^
  --use:realax.fs^
  --use:calc_int.fs^
  --use:realarith.fs^
  --use:real.fs^
  --use:calc_rat.fs^
  --use:int.fs^
  --use:sets.fs^
  --use:iterate.fs^
  --use:cart.fs^
  --use:define.fs^
  --use:help.fs^
  --use:database.fs^

:: Verify NHol.dll exists before proceeding
if exist %NHOL_ABSOLUTE% (

   :: Try to find the user's installation of F# Interactive.
   if exist %FSI_30% (
      :: VS 2012 / F# 3.0
      echo Using F# 3.0

      :: Set the 'FSI' variable to the path for F# 3.0 Interactive.
      set FSI= %FSI_30%
      set fsi_args=!fsi_args:fsi_ver=--define:FSI_VER_3!

   ) else (
      if exist %FSI_20% (
          :: VS 2010 / F# 2.0
          echo Using F# 2.0

          :: Set the 'FSI' variable to the path for F# 2.0 Interactive.
          set FSI= %FSI_20%
          set fsi_args=!fsi_args:fsi_ver=--define:FSI_VER_2!

      ) else (
          :: Unable to find the F# installation, so exit.
          echo Unable to find an installation of F# interactive at any known location.
          echo Exiting...
          pause
          exit
      )
   )
) else (

:: Unable to find NHol.dll so exit.
echo Unable to find NHol.dll at %NHOL_ABSOLUTE%.
echo.
echo Did you build NHol.dll by compiling the project?
echo If not it is suggested to use Visual Studio to automatically download NuGet packages.
echo Note: NHol works with Visual Studio Express which is free.
echo.
echo Exiting...
echo.
pause
exit
)

:: Load the NHol environment into the detected version of F# Interactive.
echo Loading NHol into F# Interactive.
%FSI% %fsi_args%
