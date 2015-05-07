set NAME=mid
set NPROBS=8
set WORKSPACE=_workspace

set LIBRARIES=%NAME%_00
set coqc="C:\Program Files (x86)\Coq\bin\coqc.exe"

:: 1. empty the workspace
RD /S /Q %WORKSPACE%
MD %WORKSPACE%

:: 2. populate the library files in the workspace
FOR %%l IN (%LIBRARIES%) DO (
	echo %%l
	copy original\%%l.v %WORKSPACE%
	call %coqc% -I %WORKSPACE% %WORKSPACE%\%%l.v
)

:: 3. for each problem number `i`,
FOR /L %%i IN (0 1 8) DO (
	echo "Problem %%i:"
	echo "submission\%NAME%_0%%i.v"

    	:: 3-1. compile the submitted version; and 
	COPY submission\%NAME%_0%%i.v %WORKSPACE%
	%coqc% -I %WORKSPACE% %WORKSPACE%\%NAME%_0%%i.v
	if ERRORLEVEL 1 (
		echo "Error! Please fix the error before submission."
		set /p end="Done."
		Exit 0
	)

    	:: 3-2. compile the original version (for later problems)
	copy original\%NAME%_0%%i.v %WORKSPACE%

	%coqc% -I %WORKSPACE% %WORKSPACE%\%NAME%_0%%i.v	
)

set /p end="Done."
