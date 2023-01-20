REM
REM overly simplified batch file to start Ant through RunAnt.jar from a command prompt
REM

@echo off

REM Set the JPF_HOME directory
set JPF_HOME=%~dp0..

set JVM_FLAGS=-Xmx1024m -ea

java %JVM_FLAGS% -jar "%JPF_HOME%\tools\RunAnt.jar" %*