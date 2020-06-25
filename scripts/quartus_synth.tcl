# PRiME pre-KAPow kernel flow
# Performs pre-KAPow run steps for instrumenting arbitrary Verilog for power monitoring
# James Davis, 2015

load_package flow

cd kernel

project_new kernel
set_global_assignment -name FAMILY "Cyclone 10 GX"
set_global_assignment -name SYSTEMVERILOG_FILE kernel.v
set_global_assignment -name TOP_LEVEL_ENTITY top
set_global_assignment -name INI_VARS "qatm_force_vqm=on;"
set_instance_assignment -name VIRTUAL_PIN ON -to *

execute_module -tool map

execute_module -tool fit

execute_module -tool eda -args "--simulation --tool=vcs"

# set_global_assignment -name POWER_OUTPUT_SAF_NAME ${kernel}.asf
# set_global_assignment -name POWER_DEFAULT_INPUT_IO_TOGGLE_RATE "12.5 %"
# set_global_assignment -name POWER_REPORT_SIGNAL_ACTIVITY ON
# set_global_assignment -name POWER_REPORT_POWER_DISSIPATION ON
# execute_module -tool pow

project_close
