<!-- markdownlint-disable -->

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/heartbeat.py#L0"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

# <kbd>module</kbd> `greed.exploration_techniques.heartbeat`






---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/heartbeat.py#L10"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

## <kbd>class</kbd> `HeartBeat`
This Exploration technique implements a Classic heartbeat. The heartbeat file will be logged during __init__. Delete such file to stop the heartbeat and get an ipdb shell. 

**Args:**
 
 - <b>`beat_interval`</b>:  the number of steps between heartbeats 
 - <b>`show_op`</b>:  show the current operation during the heartbeat 

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/heartbeat.py#L19"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `__init__`

```python
__init__(beat_interval=100, show_op=False)
```








---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/heartbeat.py#L50"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `change_beat`

```python
change_beat(new_beat_interval)
```

Change the beat interval. 

**Args:**
 
 - <b>`new_beat_interval`</b>:  the new beat interval. 

---

<a href="https://github.com/ucsb-seclab/greed/tree/main/greed/exploration_techniques/heartbeat.py#L28"><img align="right" style="float:right;" src="https://img.shields.io/badge/-source-cccccc?style=flat-square"></a>

### <kbd>method</kbd> `check_successors`

```python
check_successors(simgr, successors)
```

Check if the heartbeat should be printed. 

**Args:**
 
 - <b>`simgr`</b>:  the simulation manager 
 - <b>`successors`</b>:  the successors to check 




---

_This file was automatically generated via [lazydocs](https://github.com/ml-tooling/lazydocs)._
