(*

Copyright 2013 Jack Pappas, Anh-Dung Phan, Eric Taucher

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

// Note: To use this with F# Interactive within Visual Studio 2010
// In Visual Studio menu: Tool -> Options -> F# Tools -> F# Interactive
// For F# Interactive Options add --define:FSI_VER_2
#if FSI_VER_2
#r "./../packages/FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "./../packages/FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "./../packages/FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#r "./../packages/ExtCore.0.8.33/lib/net40/ExtCore.dll"
#r @"./../packages/NLog.2.0.1.2/lib/net40/NLog.dll"
#else
#I "./../packages"

#r "FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#r "ExtCore.0.8.33/lib/net40/ExtCore.dll"
#r @"NLog.2.0.1.2/lib/net40/NLog.dll"
#endif

// Disable "Incomplete pattern matches on this expression." warnings.
// Some of these are true warnings, but should be fixed in the code.
// No sense in seeing these warnings when using F# interactive.
#nowarn "25"

// Disable "This and other recursive references to the object(s) being defined will be checked
// for initialization-soundness at runtime through the use of a delayed reference. 
// This is because you are defining one or more recursive objects, rather than recursive functions."
#nowarn "40"

// Disable "Uppercase variable identifiers should not generally be used in patterns, and may indicate a misspelt pattern name."
#nowarn "49"

// Disable ML compatibility warnings
#nowarn "62"

open FSharp.Compatibility.OCaml;;
open FSharp.Compatibility.OCaml.Num;;
