# PRiME pre-KAPow kernel flow
# Performs pre-KAPow run steps for instrumenting arbitrary Verilog for power monitoring
# James Davis, 2015

load_package flow

project_new -overwrite syn 
set_global_assignment -name FAMILY "Arria 10"
set_global_assignment -name DEVICE 10AX115H4F34E3LG
set_global_assignment -name SYSTEMVERILOG_FILE top.v
set_global_assignment -name TOP_LEVEL_ENTITY main
#set_global_assignment -name SDC_FILE syn.sdc
#set_global_assignment -name auto_resource_sharing on
#set_global_assignment -name enable_state_machine_inference on
#set_global_assignment -name optimization_technique area
#set_global_assignment -name synthesis_effort fast
#set_global_assignment -name AUTO_RAM_RECOGNITION on
#set_global_assignment -name remove_duplicate_registers on
#set_instance_assignment -name RAMSTYLE_ATTRIBUTE LOGIC -to ram

execute_module -tool map

execute_module -tool fit

execute_module -tool sta

#execute_module -tool eda -args "--simulation --tool=vcs"

# set_global_assignment -name POWER_OUTPUT_SAF_NAME ${kernel}.asf
# set_global_assignment -name POWER_DEFAULT_INPUT_IO_TOGGLE_RATE "12.5 %"
# set_global_assignment -name POWER_REPORT_SIGNAL_ACTIVITY ON
# set_global_assignment -name POWER_REPORT_POWER_DISSIPATION ON
# execute_module -tool pow

project_close
