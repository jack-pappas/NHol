:: This batch file loads the NHol interactive environment into the
:: latest version of F# Interactive (FSI) available on this machine.

@echo off

:: Restore NuGet packages (if necessary) before proceeding.
.nuget\NuGet.exe restore NHol\packages.config -PackagesDirectory packages

if %errorlevel% neq 0 (
    echo Unable to restore NuGet packages.
    echo Exiting...
    exit /b %errorlevel%
)

:: Variables which hold paths to various versions of F# Interactive.
set FSI_30= "C:\Program Files (x86)\Microsoft SDKs\F#\3.0\Framework\v4.0\fsi.exe"
set FSI_20= "C:\Program Files (x86)\Microsoft F#\v4.0\fsi.exe"

:: Arguments to be passed to FSI, regardless of which version we're using.
set FSI_ARGS=

:: Try to find the user's installation of F# Interactive.
if exist %FSI_30% (
  :: VS 2012 / F# 3.0
  echo Using F# 3.0

  :: Set the 'FSI' variable to the path for F# 3.0 Interactive.
  set FSI= %FSI_30%

) else (
  if exist %FSI_20% (
      :: VS 2010 / F# 2.0
      echo Using F# 2.0

      :: Set the 'FSI' variable to the path for F# 2.0 Interactive.
      set FSI= %FSI_20%

  ) else (
      :: Unable to find the F# installation, so exit.
      echo Unable to find an installation of F# interactive at any known location.
      echo Exiting...
      exit
  )
)

:: Set variables which hold command-line arguments to be passed to F# Interactive.
set FSI_ARGS= %FSI_ARGS% -I:NHol^
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
  --use:database.fs
  :: NOTE : The last filename should NOT have a trailing ^ character!

:: Load the NHol environment into the detected version of F# Interactive.
echo Loading NHol into F# Interactive.
%FSI% %FSI_ARGS%
