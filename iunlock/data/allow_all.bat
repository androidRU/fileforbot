
REG DELETE "HKEY_CURRENT_USER\Software\Policies\Microsoft\Windows\System" /v DisableCMD /f

reg add "HKEY_LOCAL_MACHINE\SOFTWARE\Microsoft\Windows\CurrentVersion\Policies\Explorer" /v "NoControlPanel" /t REG_DWORD /f /d 0
rem taskkill /f /im explorer.exe
rem start explorer.exe

reg delete "HKEY_CURRENT_USER\Software\Microsoft\Windows\CurrentVersion\Policies\Attachments" /v SaveZoneInformation /f

reg add "HKEY_CURRENT_USER\SOFTWARE\Microsoft\Windows\CurrentVersion\Policies\Explorer" /v "NoClose" /t REG_DWORD /f /d 0
rem taskkill /f /im explorer.exe
rem start explorer.exe

REG DELETE "HKEY_CURRENT_USER\Software\Microsoft\Windows\CurrentVersion\Policies\System" /v DisableRegistryTools /f

reg add "HKEY_CURRENT_USER\SOFTWARE\Microsoft\Windows\CurrentVersion\Policies\System" /v "DisableTaskMgr" /t REG_DWORD /f /d 0

reg add "HKEY_CURRENT_USER\Software\Policies\Microsoft\Windows\RemovableStorageDevices" /v "Deny_All" /t REG_DWORD /f /d 0
reg add "HKEY_LOCAL_MACHINE\Software\Policies\Microsoft\Windows\RemovableStorageDevices" /v "Deny_All" /t REG_DWORD /f /d 0

