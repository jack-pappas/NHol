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

namespace Tests.NHol

/// Functions for manipulating the NHol system state to facilitate unit testing.
[<RequireQualifiedAccess>]
module internal SystemState =
    open System.Reflection
    open System.Runtime.CompilerServices


    /// Initializes NHol modules (F# modules), given a reference to the NHol assembly
    /// and a list of module names to initialize.
    let rec private initializeNHolModules (nholAssembly : Assembly) moduleNames =
        match moduleNames with
        | [] -> ()
        | moduleName :: moduleNames ->
            /// The full name (namespace + name) of the type containing the startup (initialization)
            /// code for the current NHol module (F# module).
            let moduleStartupTypeName = "<StartupCode$NHol>.$NHol." + moduleName

            // Try to get the F# module type from the map containing the types in the assembly.
            match nholAssembly.GetType (moduleStartupTypeName, false) |> Option.ofNull with
            | None ->
                // If the module's startup type couldn't be found, emit an entry to the NUnit console/log.
                printfn "Unable to initialize the '%s' module because it could not be found in the NHol assembly. (ModuleStartupTypeName = %s)"
                    moduleName moduleStartupTypeName

            | Some moduleType ->
                // Emit an entry to the NUnit console/log so we know which module we're initializing
                // in case something goes wrong during the initialization.
                printfn "Initializing the '%s' module." moduleName

                // Execute the static constructor (class constructor) for the class
                // representing the specified F# module.
                RuntimeHelpers.RunClassConstructor moduleType.TypeHandle

                // Emit an entry to the NUnit console/log stating that the module was initialized.
                printfn "Initialized the '%s' module." moduleName

            // Initialize the remaining modules.
            initializeNHolModules nholAssembly moduleNames

    /// Initializes the NHol modules in the correct order.
    /// Used to avoid issues with out-of-order initialization when running unit tests.
    let initialize () =
        // TODO : Add logging code here to record that the modules were (or weren't) initialized.
        printfn "Initializing NHol modules prior to running unit tests."

        /// The NHol assembly.
        let nholAssembly = typeof<NHol.fusion.Hol_kernel.hol_type>.Assembly

        // First initialize the module itself.
        // This isn't really necessary, since C# normally doesn't add anything to the
        // module constructor, but it doesn't hurt to be sure.
        printfn "Running the NHol module (.dll) constructor."
        RuntimeHelpers.RunModuleConstructor nholAssembly.ManifestModule.ModuleHandle
        
        // Now, initialize each of the F# modules in the NHol assembly by executing
        // the static constructor (.cctor) for the static class representing the module.
        // We use the same ordering as when loading the files into F# interactive,
        // so we should get the same results.
        initializeNHolModules nholAssembly
           ["lib";
            "fusion";
            "basics";
            "nets";
            "printer";
            "preterm";
            "parser";
            "equal";
            "bool";
            "drule";
            "tactics";
            "itab";
            "simp";
            "theorems";
            "ind_defs";
            "class";
            "trivia";
//            "canon";
//            "meson";
//            "quot";
//            "pair";
//            "nums";
//            "recursion";
//            "arith";
//            "wf";
//            "calc_num";
//            "normalizer";
//            "grobner";
//            "ind_types";
//            "lists";
//            "realax";
//            "calc_int";
//            "realarith";
//            "real";
//            "calc_rat";
//            "int";
//            "sets";
//            "iterate";
//            "cart";
//            "define";
//            "help";
//            "database";
            ]


/// Global setup/teardown for test fixtures in this project.
[<Sealed>]
[<NUnit.Framework.SetUpFixture>]
type NHolTestSetupFixture () =
    /// Forces the modules in the NHol assembly to be initialized in the correct order
    /// if they haven't been already. NUnit calls this method once prior to each test run.
    [<NUnit.Framework.SetUp>]
    member __.NHolTestsInit () =
        // Initialize the NHol modules in the correct order before running any tests.
        SystemState.initialize ()

