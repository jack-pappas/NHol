(*

Copyright 2013 Eric Taucher

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
#r @"./../packages/ExtCore.0.8.32/lib/net40/ExtCore.dll"
#r @"./../packages/NLog.2.0.1.2/lib/net40/NLog.dll"
#else
#I "./../packages"

#r @"ExtCore.0.8.32/lib/net40/ExtCore.dll"
#r "NLog.2.0.1.2/lib/net40/NLog.dll"
#endif

#load "./../NHol/Logging.fs";;

open NHol.Logging;;

Logging.configureNLogProgramatically ();;
Logging.printNLogConfig ();;

logger.Trace("trace message");;

logger.Info(Logging.alignedNameValue "Name" "Value");;

Logging.pause "I'm pausing";;