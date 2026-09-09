# Continue through finally: finally runs each time.
"""Continue through finally: finally runs each time."""
order = []
for i in range(3):
    try:
        if i == 1:
            continue
        order.append(f'body{i}')
    finally:
        order.append(f'finally{i}')

assert order == ['body0', 'finally0', 'finally1', 'body2', 'finally2'], f'got {order}'
print('PASS')
