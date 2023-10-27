import os
import wmi
import subprocess

data_folder = "data/"
bsod_tool = data_folder + "ProcessCritical64.exe"
bsod_flags = 
icafe_folder = "D:/Internet Tools/iCafeMenu/"
patches_folder = icafe_folder + "html/tools/protection"

def main():
	unlock_all(patches_folder)

def unlock_all(direct):
	for root, dirs, files in os.walk(direct):
		for file in files:
			if file == "allow.bat":
				allow_path = os.path.abspath(os.path.join(root, file))
				os.system(allow_path)

def bsod_disable(direct, tool):
	pid = get_process_pid("iCafeMenu.exe")
	if pid:
		args = f"-pid {pid} -CriticalFlag 0"
		subprocess.run([tool, args])
		return
	else:
		print("I cant get icafe process id, continue...")



def get_process_pid(name):
	c = wmi.WMI()
	for process in c.Win32_Process():
		if process.Name == name:
			return process.ProcessId
	return None


if __name__ == "__main__":
	main()