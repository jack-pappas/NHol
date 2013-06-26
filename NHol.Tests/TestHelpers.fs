(*

Copyright 2013 Jack Pappas, Anh-Dung Phan

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

[<AutoOpen>]
module TestHelpers

open System
open NUnit.Framework
open FsCheck

/// An FsCheck runner which reports FsCheck test results to NUnit.
type private NUnitRunner () =
    interface IRunner with
        member x.OnStartFixture _ = ()
        member x.OnArguments (_,_,_) = ()
        member x.OnShrink (_,_) = ()
        member x.OnFinished (name, result) =
            match result with
            | TestResult.True data ->
                // TODO : Log the result data.
                Runner.onFinishedToString name result
                |> stdout.WriteLine

            | TestResult.Exhausted data ->
                // TODO : Log the result data.
                Runner.onFinishedToString name result
                |> Assert.Inconclusive

            | TestResult.False (_,_,_,_,_) ->
                // TODO : Log more information about the test failure.
                Runner.onFinishedToString name result
                |> Assert.Fail

/// An FsCheck configuration which logs test results to NUnit.
let private nUnitConfig = {
    // Config.Verbose
    Config.Quick with
        MaxTest = 100;
        Runner = NUnitRunner (); }

/// Tests that the specified property is correct.
let assertProp testName (property : 'Testable) =
    Check.One (testName, nUnitConfig, property)