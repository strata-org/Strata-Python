from typing import Any, Dict, List, NotRequired, Required, TypedDict

_pyhard_shape_ec2_DescribeRegionsResult = TypedDict('_pyhard_shape_ec2_DescribeRegionsResult', {
    'Regions': NotRequired[List['_pyhard_shape_ec2_Region']],
})

_pyhard_shape_ec2_Region = TypedDict('_pyhard_shape_ec2_Region', {
    'OptInStatus': NotRequired[str],
    'RegionName': NotRequired[str],
    'Endpoint': NotRequired[str],
})

_pyhard_shape_dynamodb_ListTablesOutput = TypedDict('_pyhard_shape_dynamodb_ListTablesOutput', {
    'TableNames': NotRequired[List[str]],
    'LastEvaluatedTableName': NotRequired[str],
})

_pyhard_shape_dynamodb_DescribeKinesisStreamingDestinationOutput = TypedDict('_pyhard_shape_dynamodb_DescribeKinesisStreamingDestinationOutput', {
    'TableName': NotRequired[str],
    'KinesisDataStreamDestinations': NotRequired[List['_pyhard_shape_dynamodb_KinesisDataStreamDestination']],
})

_pyhard_shape_dynamodb_KinesisDataStreamDestination = TypedDict('_pyhard_shape_dynamodb_KinesisDataStreamDestination', {
    'StreamArn': NotRequired[str],
    'DestinationStatus': NotRequired[str],
    'DestinationStatusDescription': NotRequired[str],
    'ApproximateCreationDateTimePrecision': NotRequired[str],
})

_pyhard_shape_dynamodb_GetItemOutput = TypedDict('_pyhard_shape_dynamodb_GetItemOutput', {
    'Item': NotRequired[Dict[str, '_pyhard_shape_dynamodb_AttributeValue']],
    'ConsumedCapacity': NotRequired[Any],
})

_pyhard_shape_dynamodb_AttributeValue = TypedDict('_pyhard_shape_dynamodb_AttributeValue', {
    'S': NotRequired[str],
    'N': NotRequired[str],
    'B': NotRequired[str],
    'BOOL': NotRequired[bool],
    'NULL': NotRequired[bool],
    'M': NotRequired[Dict[str, '_pyhard_shape_dynamodb_AttributeValue']],
    'L': NotRequired[List['_pyhard_shape_dynamodb_AttributeValue']],
})

def _pyhard_call_ec2_DescribeRegions(*, region_name: str, params: Dict[str, Any]) -> _pyhard_shape_ec2_DescribeRegionsResult:
    ...

def _pyhard_call_dynamodb_ListTables(*, region_name: str, params: Dict[str, Any]) -> _pyhard_shape_dynamodb_ListTablesOutput:
    ...

def _pyhard_call_dynamodb_DescribeKinesisStreamingDestination(*, region_name: str, params: Dict[str, Any]) -> _pyhard_shape_dynamodb_DescribeKinesisStreamingDestinationOutput:
    ...

def _pyhard_call_dynamodb_GetItem(*, region_name: str, params: Dict[str, Any]) -> _pyhard_shape_dynamodb_GetItemOutput:
    ...
