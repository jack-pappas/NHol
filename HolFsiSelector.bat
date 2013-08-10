:: Select version of fsi to use with HOL

if exist "C:\Program Files (x86)\Microsoft SDKs\F#\3.0\Framework\v4.0\fsi.exe" (
:: FSI 11.x works with VS 2012
echo using FSI 11.x
HolFsi11.bat
) else (
if exist "C:\Program Files (x86)\Microsoft F#\v4.0\fsi.exe" (
:: FSI 2.x works with VS 2010
echo using FSI 2.x
HolFsi02.bat
) else (
ECHO Location of FSI.exe unknown
)
)



