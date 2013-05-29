(*

Copyright 2013 Jack Pappas

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

namespace NHol

/// Assembly-level attributes specific to this assembly.
module private AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("NHol.Light.Syntax")>]
    [<assembly: AssemblyDescription("An implementation of higher-order logic (HOL) in F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("3c8facf2-a8ad-454e-9821-3b45108ea8de")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("NHol.Light.Syntax.Tests")>]
    #endif

    (* Dependency hints for Ngen *)
    [<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System", LoadHint.Always)>]
    [<assembly: DependencyAttribute("ExtCore", LoadHint.Always)>]
    [<assembly: DependencyAttribute("NHol", LoadHint.Always)>]

    // Appease the F# compiler
    do ()

